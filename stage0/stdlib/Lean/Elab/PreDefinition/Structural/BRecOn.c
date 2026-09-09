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
v_options_12_ = lean_ctor_get(v___y_4_, 1);
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
v_ref_29_ = lean_ctor_get(v___y_26_, 4);
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
v_options_329_ = lean_ctor_get(v___y_326_, 1);
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
lean_object* v_toCold_333_; lean_object* v_inheritedTraceOptions_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_toCold_333_ = lean_ctor_get(v___y_326_, 0);
v_inheritedTraceOptions_334_ = lean_ctor_get(v_toCold_333_, 4);
v___x_335_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_336_ = l_Lean_Name_append(v___x_335_, v_cls_323_);
v___x_337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_334_, v_options_329_, v___x_336_);
lean_dec(v___x_336_);
v___x_338_ = lean_box(v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object* v_cls_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0(void){
_start:
{
lean_object* v___x_347_; double v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_float_of_nat(v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object* v_cls_352_, lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_405_; 
v_ref_359_ = lean_ctor_get(v___y_356_, 4);
v___x_360_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_405_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_405_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_405_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v_traceState_366_; lean_object* v_env_367_; lean_object* v_nextMacroScope_368_; lean_object* v_ngen_369_; lean_object* v_auxDeclNGen_370_; lean_object* v_cache_371_; lean_object* v_messages_372_; lean_object* v_infoState_373_; lean_object* v_snapshotTasks_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_404_; 
v___x_365_ = lean_st_ref_take(v___y_357_);
v_traceState_366_ = lean_ctor_get(v___x_365_, 4);
v_env_367_ = lean_ctor_get(v___x_365_, 0);
v_nextMacroScope_368_ = lean_ctor_get(v___x_365_, 1);
v_ngen_369_ = lean_ctor_get(v___x_365_, 2);
v_auxDeclNGen_370_ = lean_ctor_get(v___x_365_, 3);
v_cache_371_ = lean_ctor_get(v___x_365_, 5);
v_messages_372_ = lean_ctor_get(v___x_365_, 6);
v_infoState_373_ = lean_ctor_get(v___x_365_, 7);
v_snapshotTasks_374_ = lean_ctor_get(v___x_365_, 8);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_404_ == 0)
{
v___x_376_ = v___x_365_;
v_isShared_377_ = v_isSharedCheck_404_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_snapshotTasks_374_);
lean_inc(v_infoState_373_);
lean_inc(v_messages_372_);
lean_inc(v_cache_371_);
lean_inc(v_traceState_366_);
lean_inc(v_auxDeclNGen_370_);
lean_inc(v_ngen_369_);
lean_inc(v_nextMacroScope_368_);
lean_inc(v_env_367_);
lean_dec(v___x_365_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_404_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint64_t v_tid_378_; lean_object* v_traces_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_403_; 
v_tid_378_ = lean_ctor_get_uint64(v_traceState_366_, sizeof(void*)*1);
v_traces_379_ = lean_ctor_get(v_traceState_366_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_traceState_366_);
if (v_isSharedCheck_403_ == 0)
{
v___x_381_ = v_traceState_366_;
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_traces_379_);
lean_dec(v_traceState_366_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; double v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_383_ = lean_box(0);
v___x_384_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_385_ = 0;
v___x_386_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_387_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_387_, 0, v_cls_352_);
lean_ctor_set(v___x_387_, 1, v___x_383_);
lean_ctor_set(v___x_387_, 2, v___x_386_);
lean_ctor_set_float(v___x_387_, sizeof(void*)*3, v___x_384_);
lean_ctor_set_float(v___x_387_, sizeof(void*)*3 + 8, v___x_384_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*3 + 16, v___x_385_);
v___x_388_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_389_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v_a_361_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_inc(v_ref_359_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_ref_359_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = l_Lean_PersistentArray_push___redArg(v_traces_379_, v___x_390_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_391_);
v___x_393_ = v___x_381_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_391_);
lean_ctor_set_uint64(v_reuseFailAlloc_402_, sizeof(void*)*1, v_tid_378_);
v___x_393_ = v_reuseFailAlloc_402_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
lean_object* v___x_395_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 4, v___x_393_);
v___x_395_ = v___x_376_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_env_367_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_nextMacroScope_368_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_ngen_369_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_auxDeclNGen_370_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v_cache_371_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_messages_372_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_infoState_373_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_snapshotTasks_374_);
v___x_395_ = v_reuseFailAlloc_401_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_st_ref_put(v___y_357_, v___x_395_);
v___x_397_ = lean_box(0);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_397_);
v___x_399_ = v___x_363_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object* v_cls_406_, lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_406_, v_msg_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
return v_res_413_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0));
v___x_416_ = l_Lean_stringToMessageData(v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2));
v___x_419_ = l_Lean_stringToMessageData(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v___f_420_, lean_object* v_a_421_, lean_object* v_C_422_, lean_object* v_cls_423_, lean_object* v_belowDict_424_, lean_object* v_F_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___x_504_; 
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
v___x_504_ = lean_apply_5(v___f_420_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, lean_box(0));
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; uint8_t v___x_506_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
lean_inc(v_a_505_);
lean_dec_ref_known(v___x_504_, 1);
v___x_506_ = lean_unbox(v_a_505_);
lean_dec(v_a_505_);
if (v___x_506_ == 0)
{
v___y_465_ = v___y_426_;
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
v___y_468_ = v___y_429_;
goto v___jp_464_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_424_);
v___x_508_ = l_Lean_indentExpr(v_belowDict_424_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
lean_inc(v_cls_423_);
v___x_510_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_423_, v___x_509_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_dec_ref_known(v___x_510_, 1);
v___y_465_ = v___y_426_;
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
v___y_468_ = v___y_429_;
goto v___jp_464_;
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_423_);
lean_dec_ref(v_a_421_);
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_423_);
lean_dec_ref(v_a_421_);
v_a_519_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_504_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_504_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
v___jp_431_:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_isExprDefEq(v___y_432_, v_a_421_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_455_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_455_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_455_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_455_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; 
v___x_442_ = lean_unbox(v_a_438_);
lean_dec(v_a_438_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
lean_del_object(v___x_440_);
lean_dec_ref(v_F_425_);
v___x_443_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_433_, v___y_434_, v___y_435_, v___y_436_);
v_a_444_ = lean_ctor_get(v___x_443_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v___x_443_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_443_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_object* v___x_453_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_F_425_);
v___x_453_ = v___x_440_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_F_425_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_dec_ref(v_F_425_);
v_a_456_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_437_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_437_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
v___jp_464_:
{
if (lean_obj_tag(v_belowDict_424_) == 5)
{
lean_object* v_fn_469_; lean_object* v_arg_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
lean_dec(v_cls_423_);
v_fn_469_ = lean_ctor_get(v_belowDict_424_, 0);
lean_inc_ref(v_fn_469_);
v_arg_470_ = lean_ctor_get(v_belowDict_424_, 1);
lean_inc_ref(v_arg_470_);
lean_dec_ref_known(v_belowDict_424_, 2);
v___x_471_ = l_Lean_Expr_getAppFn(v_fn_469_);
lean_dec_ref(v_fn_469_);
v___x_472_ = lean_expr_eqv(v___x_471_, v_C_422_);
lean_dec_ref(v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_arg_470_);
lean_dec_ref(v_F_425_);
lean_dec_ref(v_a_421_);
v___x_473_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_465_, v___y_466_, v___y_467_, v___y_468_);
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
v___y_432_ = v_arg_470_;
v___y_433_ = v___y_465_;
v___y_434_ = v___y_466_;
v___y_435_ = v___y_467_;
v___y_436_ = v___y_468_;
goto v___jp_431_;
}
}
else
{
lean_object* v_options_482_; uint8_t v_hasTrace_483_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_a_421_);
v_options_482_ = lean_ctor_get(v___y_467_, 1);
v_hasTrace_483_ = lean_ctor_get_uint8(v_options_482_, sizeof(void*)*1);
if (v_hasTrace_483_ == 0)
{
lean_object* v___x_484_; 
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_423_);
v___x_484_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_484_;
}
else
{
lean_object* v_toCold_485_; lean_object* v_inheritedTraceOptions_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_toCold_485_ = lean_ctor_get(v___y_467_, 0);
v_inheritedTraceOptions_486_ = lean_ctor_get(v_toCold_485_, 4);
v___x_487_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_423_);
v___x_488_ = l_Lean_Name_append(v___x_487_, v_cls_423_);
v___x_489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_486_, v_options_482_, v___x_488_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_423_);
v___x_490_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_492_ = l_Lean_indentExpr(v_belowDict_424_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_423_, v___x_493_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
lean_dec_ref_known(v___x_494_, 1);
v___x_495_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_495_;
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_494_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_494_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v___f_527_, lean_object* v_a_528_, lean_object* v_C_529_, lean_object* v_cls_530_, lean_object* v_belowDict_531_, lean_object* v_F_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v___f_527_, v_a_528_, v_C_529_, v_cls_530_, v_belowDict_531_, v_F_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v_C_529_);
return v_res_538_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0(void){
_start:
{
lean_object* v___x_539_; lean_object* v_dummy_540_; 
v___x_539_ = lean_box(0);
v_dummy_540_ = l_Lean_Expr_sort___override(v___x_539_);
return v_dummy_540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_541_, lean_object* v___f_542_, lean_object* v_C_543_, lean_object* v_cls_544_, lean_object* v_F_545_, lean_object* v_xs_546_, lean_object* v_belowDict_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
uint8_t v___x_553_; lean_object* v___x_554_; 
v___x_553_ = 1;
v___x_554_ = l_Lean_Meta_zetaReduce(v_arg_541_, v___x_553_, v___x_553_, v___x_553_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___f_556_; lean_object* v_dummy_557_; lean_object* v_nargs_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc_n(v_a_555_, 2);
lean_dec_ref_known(v___x_554_, 1);
v___f_556_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_556_, 0, v___f_542_);
lean_closure_set(v___f_556_, 1, v_a_555_);
lean_closure_set(v___f_556_, 2, v_C_543_);
lean_closure_set(v___f_556_, 3, v_cls_544_);
v_dummy_557_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_558_ = l_Lean_Expr_getAppNumArgs(v_a_555_);
lean_inc(v_nargs_558_);
v___x_559_ = lean_mk_array(v_nargs_558_, v_dummy_557_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_sub(v_nargs_558_, v___x_560_);
lean_dec(v_nargs_558_);
v___x_562_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_555_, v___x_559_, v___x_561_);
v___x_575_ = lean_array_get_size(v_xs_546_);
v___x_576_ = lean_array_get_size(v___x_562_);
v___x_577_ = lean_nat_dec_le(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v___x_562_);
lean_dec_ref(v___f_556_);
lean_dec_ref(v_F_545_);
v___x_578_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_548_, v___y_549_, v___y_550_, v___y_551_);
v_a_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
v___y_564_ = v___y_548_;
v___y_565_ = v___y_549_;
v___y_566_ = v___y_550_;
v___y_567_ = v___y_551_;
goto v___jp_563_;
}
v___jp_563_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_568_ = lean_array_get_size(v___x_562_);
v___x_569_ = lean_array_get_size(v_xs_546_);
v___x_570_ = lean_nat_sub(v___x_568_, v___x_569_);
v___x_571_ = l_Array_extract___redArg(v___x_562_, v___x_570_, v___x_568_);
lean_dec_ref(v___x_562_);
v___x_572_ = l_Lean_Expr_replaceFVars(v_belowDict_547_, v_xs_546_, v___x_571_);
v___x_573_ = l_Lean_mkAppN(v_F_545_, v___x_571_);
lean_dec_ref(v___x_571_);
v___x_574_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_572_, v___x_573_, v___f_556_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_574_;
}
}
else
{
lean_dec_ref(v_F_545_);
lean_dec(v_cls_544_);
lean_dec_ref(v_C_543_);
lean_dec_ref(v___f_542_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_587_, lean_object* v___f_588_, lean_object* v_C_589_, lean_object* v_cls_590_, lean_object* v_F_591_, lean_object* v_xs_592_, lean_object* v_belowDict_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_587_, v___f_588_, v_C_589_, v_cls_590_, v_F_591_, v_xs_592_, v_belowDict_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec_ref(v_belowDict_593_);
lean_dec_ref(v_xs_592_);
return v_res_599_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0));
v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v___f_603_, lean_object* v_arg_604_, lean_object* v_C_605_, lean_object* v_cls_606_, lean_object* v_belowDict_607_, lean_object* v_F_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___x_614_; 
lean_inc_ref(v___f_603_);
lean_inc(v___y_612_);
lean_inc_ref(v___y_611_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
v___x_614_ = lean_apply_5(v___f_603_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, lean_box(0));
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___f_616_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; uint8_t v___x_624_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
lean_inc(v_cls_606_);
v___f_616_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_616_, 0, v_arg_604_);
lean_closure_set(v___f_616_, 1, v___f_603_);
lean_closure_set(v___f_616_, 2, v_C_605_);
lean_closure_set(v___f_616_, 3, v_cls_606_);
lean_closure_set(v___f_616_, 4, v_F_608_);
v___x_624_ = lean_unbox(v_a_615_);
lean_dec(v_a_615_);
if (v___x_624_ == 0)
{
lean_dec(v_cls_606_);
v___y_618_ = v___y_609_;
v___y_619_ = v___y_610_;
v___y_620_ = v___y_611_;
v___y_621_ = v___y_612_;
goto v___jp_617_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_625_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_607_);
v___x_626_ = l_Lean_indentExpr(v_belowDict_607_);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_606_, v___x_627_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_dec_ref_known(v___x_628_, 1);
v___y_618_ = v___y_609_;
v___y_619_ = v___y_610_;
v___y_620_ = v___y_611_;
v___y_621_ = v___y_612_;
goto v___jp_617_;
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v___f_616_);
lean_dec_ref(v_belowDict_607_);
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
v___jp_617_:
{
uint8_t v___x_622_; lean_object* v___x_623_; 
v___x_622_ = 0;
v___x_623_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_607_, v___f_616_, v___x_622_, v___x_622_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
return v___x_623_;
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_F_608_);
lean_dec_ref(v_belowDict_607_);
lean_dec(v_cls_606_);
lean_dec_ref(v_C_605_);
lean_dec_ref(v_arg_604_);
lean_dec_ref(v___f_603_);
v_a_637_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_614_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_614_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v___f_645_, lean_object* v_arg_646_, lean_object* v_C_647_, lean_object* v_cls_648_, lean_object* v_belowDict_649_, lean_object* v_F_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v___f_645_, v_arg_646_, v_C_647_, v_cls_648_, v_belowDict_649_, v_F_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_656_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_668_ = l_Lean_stringToMessageData(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_672_, lean_object* v_belowDict_673_, lean_object* v_arg_674_, lean_object* v_F_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_cls_681_; lean_object* v___f_682_; lean_object* v___x_683_; lean_object* v_a_684_; lean_object* v___f_685_; uint8_t v___x_686_; 
v_cls_681_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_682_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
v___x_683_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_681_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref(v___x_683_);
lean_inc_ref(v_arg_674_);
v___f_685_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_685_, 0, v___f_682_);
lean_closure_set(v___f_685_, 1, v_arg_674_);
lean_closure_set(v___f_685_, 2, v_C_672_);
lean_closure_set(v___f_685_, 3, v_cls_681_);
v___x_686_ = lean_unbox(v_a_684_);
lean_dec(v_a_684_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec_ref(v_arg_674_);
v___x_687_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_673_, v_F_675_, v___f_685_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_688_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_673_);
v___x_689_ = l_Lean_indentExpr(v_belowDict_673_);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
v___x_693_ = l_Lean_indentExpr(v_arg_674_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_681_, v___x_694_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v___x_696_; 
lean_dec_ref_known(v___x_695_, 1);
v___x_696_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_673_, v_F_675_, v___f_685_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
return v___x_696_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v___f_685_);
lean_dec_ref(v_F_675_);
lean_dec_ref(v_belowDict_673_);
v_a_697_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_695_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_705_, lean_object* v_belowDict_706_, lean_object* v_arg_707_, lean_object* v_F_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_705_, v_belowDict_706_, v_arg_707_, v_F_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v___x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_options_721_; uint8_t v_hasTrace_722_; 
v_options_721_ = lean_ctor_get(v___y_718_, 1);
v_hasTrace_722_ = lean_ctor_get_uint8(v_options_721_, sizeof(void*)*1);
if (v_hasTrace_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v___x_715_);
v___x_723_ = lean_box(v_hasTrace_722_);
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_toCold_725_; lean_object* v_inheritedTraceOptions_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_toCold_725_ = lean_ctor_get(v___y_718_, 0);
v_inheritedTraceOptions_726_ = lean_ctor_get(v_toCold_725_, 4);
v___x_727_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_728_ = l_Lean_Name_append(v___x_727_, v___x_715_);
v___x_729_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_726_, v_options_721_, v___x_728_);
lean_dec(v___x_728_);
v___x_730_ = lean_box(v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v___x_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_739_, lean_object* v_x_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v_t_739_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_747_, v_x_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_x_748_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v_t_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__1));
v___x_765_ = l_Lean_Core_mkFreshUserName(v___x_764_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_775_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___f_770_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_770_, 0, v_t_758_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_a_766_);
lean_ctor_set(v___x_771_, 1, v___f_770_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_t_758_);
v_a_776_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_765_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_765_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v_t_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v_t_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_791_, lean_object* v_a_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_array_set(v___y_794_, v_a_792_, v___x_791_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_803_, lean_object* v_a_804_, lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_803_, v_a_804_, v_x_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v_a_804_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_813_, lean_object* v_a_814_, lean_object* v_x_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_snd_822_; lean_object* v_fst_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_874_; 
v_snd_822_ = lean_ctor_get(v___y_816_, 1);
v_fst_823_ = lean_ctor_get(v___y_816_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___y_816_);
if (v_isSharedCheck_874_ == 0)
{
v___x_825_ = v___y_816_;
v_isShared_826_ = v_isSharedCheck_874_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_snd_822_);
lean_inc(v_fst_823_);
lean_dec(v___y_816_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_874_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_array_827_; lean_object* v_start_828_; lean_object* v_stop_829_; uint8_t v___x_830_; 
v_array_827_ = lean_ctor_get(v_snd_822_, 0);
v_start_828_ = lean_ctor_get(v_snd_822_, 1);
v_stop_829_ = lean_ctor_get(v_snd_822_, 2);
v___x_830_ = lean_nat_dec_lt(v_start_828_, v_stop_829_);
if (v___x_830_ == 0)
{
lean_object* v___x_832_; 
lean_dec_ref(v_a_814_);
lean_dec_ref(v___x_813_);
if (v_isShared_826_ == 0)
{
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_fst_823_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_snd_822_);
v___x_832_ = v_reuseFailAlloc_835_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
return v___x_834_;
}
}
else
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_870_; 
lean_inc(v_stop_829_);
lean_inc(v_start_828_);
lean_inc_ref(v_array_827_);
v_isSharedCheck_870_ = !lean_is_exclusive(v_snd_822_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; lean_object* v_unused_872_; lean_object* v_unused_873_; 
v_unused_871_ = lean_ctor_get(v_snd_822_, 2);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_snd_822_, 1);
lean_dec(v_unused_872_);
v_unused_873_ = lean_ctor_get(v_snd_822_, 0);
lean_dec(v_unused_873_);
v___x_837_ = v_snd_822_;
v_isShared_838_ = v_isSharedCheck_870_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_snd_822_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_870_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___f_840_; size_t v_sz_841_; size_t v___x_842_; lean_object* v___x_7106__overap_843_; lean_object* v___x_844_; 
v___x_839_ = lean_array_fget_borrowed(v_array_827_, v_start_828_);
lean_inc(v___x_839_);
v___f_840_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_840_, 0, v___x_839_);
v_sz_841_ = lean_array_size(v_a_814_);
v___x_842_ = ((size_t)0ULL);
v___x_7106__overap_843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_813_, v_a_814_, v___f_840_, v_sz_841_, v___x_842_, v_fst_823_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
v___x_844_ = lean_apply_5(v___x_7106__overap_843_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, lean_box(0));
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_861_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_861_ == 0)
{
v___x_847_ = v___x_844_;
v_isShared_848_ = v_isSharedCheck_861_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_844_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_861_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_start_828_, v___x_849_);
lean_dec(v_start_828_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_850_);
v___x_852_ = v___x_837_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_array_827_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_stop_829_);
v___x_852_ = v_reuseFailAlloc_860_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v___x_852_);
lean_ctor_set(v___x_825_, 0, v_a_845_);
v___x_854_ = v___x_825_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_845_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_852_);
v___x_854_ = v_reuseFailAlloc_859_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_855_);
v___x_857_ = v___x_847_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_del_object(v___x_837_);
lean_dec(v_stop_829_);
lean_dec(v_start_828_);
lean_dec_ref(v_array_827_);
lean_del_object(v___x_825_);
v_a_862_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_844_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_844_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_875_, lean_object* v_a_876_, lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_875_, v_a_876_, v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_884_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_positions_898_, lean_object* v_a_899_, lean_object* v___f_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v_k_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v_toMonadRef_906_, lean_object* v___x_907_, lean_object* v_Cs_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_7133__overap_915_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_908_);
lean_inc_ref(v___x_896_);
v___x_7133__overap_915_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_896_, v___x_897_, v___x_914_, v_positions_898_, v_a_899_, v_Cs_908_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
v___x_916_ = lean_apply_5(v___x_7133__overap_915_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
v___x_918_ = lean_apply_5(v___f_900_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; uint8_t v___x_961_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v___x_920_ = l_Lean_mkAppN(v___x_901_, v_a_917_);
lean_dec(v_a_917_);
v___x_921_ = l_Subarray_copy___redArg(v___x_902_);
v___x_922_ = l_Lean_mkAppN(v___x_920_, v___x_921_);
lean_dec_ref(v___x_921_);
v___x_961_ = lean_unbox(v_a_919_);
lean_dec(v_a_919_);
if (v___x_961_ == 0)
{
v___y_924_ = v___y_909_;
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
v___y_927_ = v___y_912_;
goto v___jp_923_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_7183__overap_973_; lean_object* v___x_974_; 
v___x_962_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_908_);
v___x_963_ = lean_array_to_list(v_Cs_908_);
v___x_964_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_965_ = lean_box(0);
v___x_966_ = l_List_mapTR_loop___redArg(v___x_964_, v___x_963_, v___x_965_);
v___x_967_ = l_Lean_MessageData_ofList(v___x_966_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_962_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
lean_inc_ref(v___x_922_);
v___x_971_ = l_Lean_indentExpr(v___x_922_);
v___x_972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
lean_inc(v___x_904_);
lean_inc_ref(v___x_907_);
lean_inc_ref(v_toMonadRef_906_);
lean_inc_ref(v___x_905_);
lean_inc_ref(v___x_896_);
v___x_7183__overap_973_ = l_Lean_addTrace___redArg(v___x_896_, v___x_905_, v_toMonadRef_906_, v___x_907_, v___x_904_, v___x_972_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
v___x_974_ = lean_apply_5(v___x_7183__overap_973_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_974_) == 0)
{
lean_dec_ref_known(v___x_974_, 1);
v___y_924_ = v___y_909_;
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
v___y_927_ = v___y_912_;
goto v___jp_923_;
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___x_922_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_toMonadRef_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_896_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
v___jp_923_:
{
lean_object* v___x_928_; 
lean_inc_ref(v___x_922_);
v___x_928_ = l_Lean_Meta_isTypeCorrect(v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref_known(v___x_928_, 1);
v___x_930_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
if (v___x_930_ == 0)
{
lean_object* v_options_931_; uint8_t v_hasTrace_932_; 
v_options_931_ = lean_ctor_get(v___y_926_, 1);
v_hasTrace_932_ = lean_ctor_get_uint8(v_options_931_, sizeof(void*)*1);
if (v_hasTrace_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec_ref(v___x_907_);
lean_dec_ref(v_toMonadRef_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v___x_896_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_933_ = lean_apply_7(v_k_903_, v_Cs_908_, v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_933_;
}
else
{
lean_object* v_toCold_934_; lean_object* v_inheritedTraceOptions_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_toCold_934_ = lean_ctor_get(v___y_926_, 0);
v_inheritedTraceOptions_935_ = lean_ctor_get(v_toCold_934_, 4);
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_904_);
v___x_937_ = l_Lean_Name_append(v___x_936_, v___x_904_);
v___x_938_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_935_, v_options_931_, v___x_937_);
lean_dec(v___x_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec_ref(v___x_907_);
lean_dec_ref(v_toMonadRef_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v___x_896_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_939_ = lean_apply_7(v_k_903_, v_Cs_908_, v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_939_;
}
else
{
lean_object* v___x_940_; lean_object* v___x_7159__overap_941_; lean_object* v___x_942_; 
v___x_940_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_7159__overap_941_ = l_Lean_addTrace___redArg(v___x_896_, v___x_905_, v_toMonadRef_906_, v___x_907_, v___x_904_, v___x_940_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_942_ = lean_apply_5(v___x_7159__overap_941_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v___x_943_; 
lean_dec_ref_known(v___x_942_, 1);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_943_ = lean_apply_7(v_k_903_, v_Cs_908_, v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_943_;
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v___x_922_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v_k_903_);
v_a_944_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_942_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_942_);
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
}
else
{
lean_object* v___x_952_; 
lean_dec_ref(v___x_907_);
lean_dec_ref(v_toMonadRef_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v___x_896_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_952_ = lean_apply_7(v_k_903_, v_Cs_908_, v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_952_;
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v___x_922_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_toMonadRef_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_896_);
v_a_953_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_928_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_928_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_917_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_toMonadRef_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_896_);
v_a_983_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_918_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_918_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec_ref(v_toMonadRef_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___f_900_);
lean_dec_ref(v___x_896_);
v_a_991_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_916_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_916_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_999_ = _args[0];
lean_object* v___x_1000_ = _args[1];
lean_object* v_positions_1001_ = _args[2];
lean_object* v_a_1002_ = _args[3];
lean_object* v___f_1003_ = _args[4];
lean_object* v___x_1004_ = _args[5];
lean_object* v___x_1005_ = _args[6];
lean_object* v_k_1006_ = _args[7];
lean_object* v___x_1007_ = _args[8];
lean_object* v___x_1008_ = _args[9];
lean_object* v_toMonadRef_1009_ = _args[10];
lean_object* v___x_1010_ = _args[11];
lean_object* v_Cs_1011_ = _args[12];
lean_object* v___y_1012_ = _args[13];
lean_object* v___y_1013_ = _args[14];
lean_object* v___y_1014_ = _args[15];
lean_object* v___y_1015_ = _args[16];
lean_object* v___y_1016_ = _args[17];
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_999_, v___x_1000_, v_positions_1001_, v_a_1002_, v___f_1003_, v___x_1004_, v___x_1005_, v_k_1006_, v___x_1007_, v___x_1008_, v_toMonadRef_1009_, v___x_1010_, v_Cs_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(37u);
v___x_1019_ = l_Lean_Level_ofNat(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1021_ = l_Lean_Expr_sort___override(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1028_, lean_object* v___x_1029_, lean_object* v___f_1030_, lean_object* v___f_1031_, lean_object* v___x_1032_, lean_object* v_numTypeFormers_1033_, lean_object* v___f_1034_, lean_object* v___x_1035_, lean_object* v_k_1036_, lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_toMonadRef_1039_, lean_object* v___x_1040_, lean_object* v_numIndParams_1041_, lean_object* v_a_1042_, lean_object* v_f_1043_, lean_object* v_args_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1056_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___x_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = lean_nat_add(v_numIndParams_1041_, v_numTypeFormers_1033_);
v___x_1177_ = lean_array_get_size(v_args_1044_);
v___x_1178_ = lean_nat_dec_lt(v___x_1176_, v___x_1177_);
lean_dec(v___x_1176_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v_args_1044_);
lean_dec_ref(v_f_1043_);
lean_dec(v_numIndParams_1041_);
lean_dec_ref(v_k_1036_);
lean_dec_ref(v___x_1035_);
lean_dec(v_numTypeFormers_1033_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___f_1030_);
lean_dec_ref(v_positions_1028_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
v___x_1179_ = lean_apply_5(v___f_1034_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; uint8_t v___x_1181_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref_known(v___x_1179_, 1);
v___x_1181_ = lean_unbox(v_a_1180_);
lean_dec(v_a_1180_);
if (v___x_1181_ == 0)
{
lean_dec_ref(v_a_1042_);
lean_dec_ref(v___x_1040_);
lean_dec_ref(v_toMonadRef_1039_);
lean_dec_ref(v___x_1038_);
lean_dec(v___x_1037_);
lean_dec_ref(v___x_1029_);
v___y_1163_ = v___y_1045_;
v___y_1164_ = v___y_1046_;
v___y_1165_ = v___y_1047_;
v___y_1166_ = v___y_1048_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_7315__overap_1185_; lean_object* v___x_1186_; 
v___x_1182_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1183_ = l_Lean_indentExpr(v_a_1042_);
v___x_1184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_7315__overap_1185_ = l_Lean_addTrace___redArg(v___x_1029_, v___x_1038_, v_toMonadRef_1039_, v___x_1040_, v___x_1037_, v___x_1184_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
v___x_1186_ = lean_apply_5(v___x_7315__overap_1185_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, lean_box(0));
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_dec_ref_known(v___x_1186_, 1);
v___y_1163_ = v___y_1045_;
v___y_1164_ = v___y_1046_;
v___y_1165_ = v___y_1047_;
v___y_1166_ = v___y_1048_;
goto v___jp_1162_;
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
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
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v_a_1042_);
lean_dec_ref(v___x_1040_);
lean_dec_ref(v_toMonadRef_1039_);
lean_dec_ref(v___x_1038_);
lean_dec(v___x_1037_);
lean_dec_ref(v___x_1029_);
v_a_1195_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1179_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1179_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
else
{
lean_dec_ref(v_a_1042_);
v___y_1151_ = v___y_1045_;
v___y_1152_ = v___y_1046_;
v___y_1153_ = v___y_1047_;
v___y_1154_ = v___y_1048_;
goto v___jp_1150_;
}
v___jp_1050_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; size_t v_sz_1064_; size_t v___x_1065_; lean_object* v___x_7228__overap_1066_; lean_object* v___x_1067_; 
v___x_1059_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1060_ = lean_mk_array(v___y_1051_, v___x_1059_);
v___x_1061_ = lean_array_get_size(v___y_1052_);
v___x_1062_ = l_Array_toSubarray___redArg(v___y_1052_, v___y_1054_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v_sz_1064_ = lean_array_size(v_positions_1028_);
v___x_1065_ = ((size_t)0ULL);
lean_inc_ref(v___x_1029_);
v___x_7228__overap_1066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1029_, v_positions_1028_, v___f_1030_, v_sz_1064_, v___x_1065_, v___x_1063_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
v___x_1067_ = lean_apply_5(v___x_7228__overap_1066_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, lean_box(0));
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v_fst_1069_; size_t v_sz_1070_; lean_object* v___x_7231__overap_1071_; lean_object* v___x_1072_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v_fst_1069_ = lean_ctor_get(v_a_1068_, 0);
lean_inc(v_fst_1069_);
lean_dec(v_a_1068_);
v_sz_1070_ = lean_array_size(v_fst_1069_);
lean_inc_ref(v___x_1029_);
v___x_7231__overap_1071_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1029_, v___f_1031_, v_sz_1070_, v___x_1065_, v_fst_1069_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
v___x_1072_ = lean_apply_5(v___x_7231__overap_1071_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, lean_box(0));
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; uint8_t v___x_1074_; lean_object* v___x_7235__overap_1075_; lean_object* v___x_1076_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_a_1073_);
lean_dec_ref_known(v___x_1072_, 1);
v___x_1074_ = 0;
v___x_7235__overap_1075_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1032_, v___x_1029_, v_a_1073_, v___y_1053_, v___x_1074_);
lean_inc(v___y_1058_);
lean_inc_ref(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc_ref(v___y_1055_);
v___x_1076_ = lean_apply_5(v___x_7235__overap_1075_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, lean_box(0));
return v___x_1076_;
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v___y_1053_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___x_1029_);
v_a_1077_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1072_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1072_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec_ref(v___y_1053_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___x_1029_);
v_a_1085_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1067_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1067_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
v___jp_1093_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = l_Subarray_copy___redArg(v___y_1099_);
v___x_1102_ = l_Lean_mkAppN(v_f_1043_, v___x_1101_);
lean_dec_ref(v___x_1101_);
lean_inc_ref(v___x_1102_);
v___x_1103_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1033_, v___x_1102_, v___y_1095_, v___y_1096_, v___y_1094_, v___y_1097_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; lean_object* v___x_1105_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
lean_dec_ref_known(v___x_1103_, 1);
lean_inc_ref(v___f_1034_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1094_);
lean_inc(v___y_1096_);
lean_inc_ref(v___y_1095_);
v___x_1105_ = lean_apply_5(v___f_1034_, v___y_1095_, v___y_1096_, v___y_1094_, v___y_1097_, lean_box(0));
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_lower_1107_; lean_object* v_upper_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1133_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_lower_1107_ = lean_ctor_get(v___y_1100_, 0);
v_upper_1108_ = lean_ctor_get(v___y_1100_, 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___y_1100_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1110_ = v___y_1100_;
v_isShared_1111_ = v_isSharedCheck_1133_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_upper_1108_);
lean_inc(v_lower_1107_);
lean_dec(v___y_1100_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1133_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1112_ = l_Array_toSubarray___redArg(v_args_1044_, v_lower_1107_, v_upper_1108_);
lean_inc_ref(v___x_1040_);
lean_inc_ref(v_toMonadRef_1039_);
lean_inc_ref(v___x_1038_);
lean_inc(v___x_1037_);
lean_inc(v_a_1104_);
lean_inc_ref(v_positions_1028_);
lean_inc_ref(v___x_1029_);
v___f_1113_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1113_, 0, v___x_1029_);
lean_closure_set(v___f_1113_, 1, v___x_1035_);
lean_closure_set(v___f_1113_, 2, v_positions_1028_);
lean_closure_set(v___f_1113_, 3, v_a_1104_);
lean_closure_set(v___f_1113_, 4, v___f_1034_);
lean_closure_set(v___f_1113_, 5, v___x_1102_);
lean_closure_set(v___f_1113_, 6, v___x_1112_);
lean_closure_set(v___f_1113_, 7, v_k_1036_);
lean_closure_set(v___f_1113_, 8, v___x_1037_);
lean_closure_set(v___f_1113_, 9, v___x_1038_);
lean_closure_set(v___f_1113_, 10, v_toMonadRef_1039_);
lean_closure_set(v___f_1113_, 11, v___x_1040_);
v___x_1114_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1028_);
v___x_1115_ = lean_unbox(v_a_1106_);
lean_dec(v_a_1106_);
if (v___x_1115_ == 0)
{
lean_del_object(v___x_1110_);
lean_dec_ref(v___x_1040_);
lean_dec_ref(v_toMonadRef_1039_);
lean_dec_ref(v___x_1038_);
lean_dec(v___x_1037_);
v___y_1051_ = v___x_1114_;
v___y_1052_ = v_a_1104_;
v___y_1053_ = v___f_1113_;
v___y_1054_ = v___y_1098_;
v___y_1055_ = v___y_1095_;
v___y_1056_ = v___y_1096_;
v___y_1057_ = v___y_1094_;
v___y_1058_ = v___y_1097_;
goto v___jp_1050_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1116_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1114_);
v___x_1117_ = l_Nat_reprFast(v___x_1114_);
v___x_1118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
v___x_1119_ = l_Lean_MessageData_ofFormat(v___x_1118_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set_tag(v___x_1110_, 7);
lean_ctor_set(v___x_1110_, 1, v___x_1119_);
lean_ctor_set(v___x_1110_, 0, v___x_1116_);
v___x_1121_ = v___x_1110_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1116_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_7268__overap_1122_; lean_object* v___x_1123_; 
lean_inc_ref(v___x_1029_);
v___x_7268__overap_1122_ = l_Lean_addTrace___redArg(v___x_1029_, v___x_1038_, v_toMonadRef_1039_, v___x_1040_, v___x_1037_, v___x_1121_);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1094_);
lean_inc(v___y_1096_);
lean_inc_ref(v___y_1095_);
v___x_1123_ = lean_apply_5(v___x_7268__overap_1122_, v___y_1095_, v___y_1096_, v___y_1094_, v___y_1097_, lean_box(0));
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_dec_ref_known(v___x_1123_, 1);
v___y_1051_ = v___x_1114_;
v___y_1052_ = v_a_1104_;
v___y_1053_ = v___f_1113_;
v___y_1054_ = v___y_1098_;
v___y_1055_ = v___y_1095_;
v___y_1056_ = v___y_1096_;
v___y_1057_ = v___y_1094_;
v___y_1058_ = v___y_1097_;
goto v___jp_1050_;
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v___x_1114_);
lean_dec_ref(v___f_1113_);
lean_dec(v_a_1104_);
lean_dec(v___y_1098_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___f_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_positions_1028_);
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
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
}
}
}
else
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_a_1104_);
lean_dec_ref(v___x_1102_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1098_);
lean_dec_ref(v_args_1044_);
lean_dec_ref(v___x_1040_);
lean_dec_ref(v_toMonadRef_1039_);
lean_dec_ref(v___x_1038_);
lean_dec(v___x_1037_);
lean_dec_ref(v_k_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___f_1034_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___f_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_positions_1028_);
v_a_1134_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1105_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1105_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v___x_1102_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1098_);
lean_dec_ref(v_args_1044_);
lean_dec_ref(v___x_1040_);
lean_dec_ref(v_toMonadRef_1039_);
lean_dec_ref(v___x_1038_);
lean_dec(v___x_1037_);
lean_dec_ref(v_k_1036_);
lean_dec_ref(v___x_1035_);
lean_dec_ref(v___f_1034_);
lean_dec_ref(v___x_1032_);
lean_dec_ref(v___f_1031_);
lean_dec_ref(v___f_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_positions_1028_);
v_a_1142_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1103_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1103_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
v___jp_1150_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1041_);
lean_inc_ref(v_args_1044_);
v___x_1156_ = l_Array_toSubarray___redArg(v_args_1044_, v___x_1155_, v_numIndParams_1041_);
v___x_1157_ = lean_nat_add(v_numIndParams_1041_, v_numTypeFormers_1033_);
lean_dec(v_numIndParams_1041_);
v___x_1158_ = lean_array_get_size(v_args_1044_);
v___x_1159_ = lean_nat_dec_le(v___x_1157_, v___x_1155_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1157_);
lean_ctor_set(v___x_1160_, 1, v___x_1158_);
v___y_1094_ = v___y_1153_;
v___y_1095_ = v___y_1151_;
v___y_1096_ = v___y_1152_;
v___y_1097_ = v___y_1154_;
v___y_1098_ = v___x_1155_;
v___y_1099_ = v___x_1156_;
v___y_1100_ = v___x_1160_;
goto v___jp_1093_;
}
else
{
lean_object* v___x_1161_; 
lean_dec(v___x_1157_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1155_);
lean_ctor_set(v___x_1161_, 1, v___x_1158_);
v___y_1094_ = v___y_1153_;
v___y_1095_ = v___y_1151_;
v___y_1096_ = v___y_1152_;
v___y_1097_ = v___y_1154_;
v___y_1098_ = v___x_1155_;
v___y_1099_ = v___x_1156_;
v___y_1100_ = v___x_1161_;
goto v___jp_1093_;
}
}
v___jp_1162_:
{
lean_object* v___x_1167_; lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v___x_1167_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1167_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1203_ = _args[0];
lean_object* v___x_1204_ = _args[1];
lean_object* v___f_1205_ = _args[2];
lean_object* v___f_1206_ = _args[3];
lean_object* v___x_1207_ = _args[4];
lean_object* v_numTypeFormers_1208_ = _args[5];
lean_object* v___f_1209_ = _args[6];
lean_object* v___x_1210_ = _args[7];
lean_object* v_k_1211_ = _args[8];
lean_object* v___x_1212_ = _args[9];
lean_object* v___x_1213_ = _args[10];
lean_object* v_toMonadRef_1214_ = _args[11];
lean_object* v___x_1215_ = _args[12];
lean_object* v_numIndParams_1216_ = _args[13];
lean_object* v_a_1217_ = _args[14];
lean_object* v_f_1218_ = _args[15];
lean_object* v_args_1219_ = _args[16];
lean_object* v___y_1220_ = _args[17];
lean_object* v___y_1221_ = _args[18];
lean_object* v___y_1222_ = _args[19];
lean_object* v___y_1223_ = _args[20];
lean_object* v___y_1224_ = _args[21];
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1203_, v___x_1204_, v___f_1205_, v___f_1206_, v___x_1207_, v_numTypeFormers_1208_, v___f_1209_, v___x_1210_, v_k_1211_, v___x_1212_, v___x_1213_, v_toMonadRef_1214_, v___x_1215_, v_numIndParams_1216_, v_a_1217_, v_f_1218_, v_args_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_instMonadEIO(lean_box(0));
return v___x_1226_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1228_ = l_StateRefT_x27_instMonad___redArg(v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1237_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1236_, v___x_1235_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___f_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1240_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1239_, v___x_1238_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1244_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1245_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1246_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1245_, v___x_1244_, v___x_1243_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___f_1248_; lean_object* v___f_1249_; lean_object* v___x_1250_; 
v___x_1247_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1248_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1250_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1249_, v___f_1248_, v___x_1247_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1257_, lean_object* v_numIndParams_1258_, lean_object* v_positions_1259_, lean_object* v_k_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___x_1266_; lean_object* v_toApplicative_1267_; lean_object* v_toFunctor_1268_; lean_object* v_toSeq_1269_; lean_object* v_toSeqLeft_1270_; lean_object* v_toSeqRight_1271_; lean_object* v___f_1272_; lean_object* v___f_1273_; lean_object* v___f_1274_; lean_object* v___f_1275_; lean_object* v___x_1276_; lean_object* v___f_1277_; lean_object* v___f_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_toApplicative_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1405_; 
v___x_1266_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1267_ = lean_ctor_get(v___x_1266_, 0);
v_toFunctor_1268_ = lean_ctor_get(v_toApplicative_1267_, 0);
v_toSeq_1269_ = lean_ctor_get(v_toApplicative_1267_, 2);
v_toSeqLeft_1270_ = lean_ctor_get(v_toApplicative_1267_, 3);
v_toSeqRight_1271_ = lean_ctor_get(v_toApplicative_1267_, 4);
v___f_1272_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1273_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1268_, 2);
v___f_1274_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1274_, 0, v_toFunctor_1268_);
v___f_1275_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1275_, 0, v_toFunctor_1268_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___f_1274_);
lean_ctor_set(v___x_1276_, 1, v___f_1275_);
lean_inc(v_toSeqRight_1271_);
v___f_1277_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1277_, 0, v_toSeqRight_1271_);
lean_inc(v_toSeqLeft_1270_);
v___f_1278_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1278_, 0, v_toSeqLeft_1270_);
lean_inc(v_toSeq_1269_);
v___f_1279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1279_, 0, v_toSeq_1269_);
v___x_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1276_);
lean_ctor_set(v___x_1280_, 1, v___f_1272_);
lean_ctor_set(v___x_1280_, 2, v___f_1279_);
lean_ctor_set(v___x_1280_, 3, v___f_1278_);
lean_ctor_set(v___x_1280_, 4, v___f_1277_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___f_1273_);
v___x_1282_ = l_StateRefT_x27_instMonad___redArg(v___x_1281_);
v_toApplicative_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1282_, 1);
lean_dec(v_unused_1406_);
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1405_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_toApplicative_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1405_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_toFunctor_1287_; lean_object* v_toSeq_1288_; lean_object* v_toSeqLeft_1289_; lean_object* v_toSeqRight_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1403_; 
v_toFunctor_1287_ = lean_ctor_get(v_toApplicative_1283_, 0);
v_toSeq_1288_ = lean_ctor_get(v_toApplicative_1283_, 2);
v_toSeqLeft_1289_ = lean_ctor_get(v_toApplicative_1283_, 3);
v_toSeqRight_1290_ = lean_ctor_get(v_toApplicative_1283_, 4);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_toApplicative_1283_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_toApplicative_1283_, 1);
lean_dec(v_unused_1404_);
v___x_1292_ = v_toApplicative_1283_;
v_isShared_1293_ = v_isSharedCheck_1403_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_toSeqRight_1290_);
lean_inc(v_toSeqLeft_1289_);
lean_inc(v_toSeq_1288_);
lean_inc(v_toFunctor_1287_);
lean_dec(v_toApplicative_1283_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1403_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___f_1297_; lean_object* v___x_1298_; lean_object* v___f_1299_; lean_object* v___f_1300_; lean_object* v___f_1301_; lean_object* v___x_1303_; 
v___f_1294_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1287_);
v___f_1296_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1296_, 0, v_toFunctor_1287_);
v___f_1297_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1297_, 0, v_toFunctor_1287_);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___f_1296_);
lean_ctor_set(v___x_1298_, 1, v___f_1297_);
v___f_1299_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1299_, 0, v_toSeqRight_1290_);
v___f_1300_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1300_, 0, v_toSeqLeft_1289_);
v___f_1301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1301_, 0, v_toSeq_1288_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 4, v___f_1299_);
lean_ctor_set(v___x_1292_, 3, v___f_1300_);
lean_ctor_set(v___x_1292_, 2, v___f_1301_);
lean_ctor_set(v___x_1292_, 1, v___f_1294_);
lean_ctor_set(v___x_1292_, 0, v___x_1298_);
v___x_1303_ = v___x_1292_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___f_1294_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v___f_1301_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v___f_1300_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v___f_1299_);
v___x_1303_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___f_1295_);
lean_ctor_set(v___x_1285_, 0, v___x_1303_);
v___x_1305_ = v___x_1285_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___f_1295_);
v___x_1305_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v_toApplicative_1307_; lean_object* v_toFunctor_1308_; lean_object* v_toSeq_1309_; lean_object* v_toSeqLeft_1310_; lean_object* v_toSeqRight_1311_; lean_object* v___f_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___f_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_toMonadRef_1324_; lean_object* v___x_1325_; 
v___x_1306_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1307_ = lean_ctor_get(v___x_1266_, 0);
v_toFunctor_1308_ = lean_ctor_get(v_toApplicative_1307_, 0);
v_toSeq_1309_ = lean_ctor_get(v_toApplicative_1307_, 2);
v_toSeqLeft_1310_ = lean_ctor_get(v_toApplicative_1307_, 3);
v_toSeqRight_1311_ = lean_ctor_get(v_toApplicative_1307_, 4);
lean_inc_ref_n(v_toFunctor_1308_, 2);
v___f_1312_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1312_, 0, v_toFunctor_1308_);
v___f_1313_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1313_, 0, v_toFunctor_1308_);
v___x_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___f_1312_);
lean_ctor_set(v___x_1314_, 1, v___f_1313_);
lean_inc(v_toSeqRight_1311_);
v___f_1315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1315_, 0, v_toSeqRight_1311_);
lean_inc(v_toSeqLeft_1310_);
v___f_1316_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1316_, 0, v_toSeqLeft_1310_);
lean_inc(v_toSeq_1309_);
v___f_1317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1317_, 0, v_toSeq_1309_);
v___x_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1314_);
lean_ctor_set(v___x_1318_, 1, v___f_1272_);
lean_ctor_set(v___x_1318_, 2, v___f_1317_);
lean_ctor_set(v___x_1318_, 3, v___f_1316_);
lean_ctor_set(v___x_1318_, 4, v___f_1315_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___f_1273_);
v___x_1320_ = l_StateRefT_x27_instMonad___redArg(v___x_1319_);
v___x_1321_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1321_, 0, lean_box(0));
lean_closure_set(v___x_1321_, 1, lean_box(0));
lean_closure_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = l_instMonadControlTOfPure___redArg(v___x_1321_);
v___x_1323_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1264_);
lean_inc_ref(v_a_1263_);
lean_inc(v_a_1262_);
lean_inc_ref(v_a_1261_);
lean_inc_ref(v_below_1257_);
v___x_1325_ = lean_infer_type(v_below_1257_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v_a_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_numTypeFormers_1335_; lean_object* v___f_1336_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; uint8_t v___x_1379_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc_n(v_a_1326_, 2);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
v___x_1329_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1327_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1329_);
v___f_1331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref_n(v___x_1305_, 2);
v___f_1332_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed), 9, 1);
lean_closure_set(v___f_1332_, 0, v___x_1305_);
v___x_1333_ = l_Lean_instInhabitedExpr;
v___x_1334_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1335_ = lean_array_get_size(v_positions_1259_);
lean_inc_ref(v_toMonadRef_1324_);
v___f_1336_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1336_, 0, v_positions_1259_);
lean_closure_set(v___f_1336_, 1, v___x_1305_);
lean_closure_set(v___f_1336_, 2, v___f_1332_);
lean_closure_set(v___f_1336_, 3, v___f_1331_);
lean_closure_set(v___f_1336_, 4, v___x_1322_);
lean_closure_set(v___f_1336_, 5, v_numTypeFormers_1335_);
lean_closure_set(v___f_1336_, 6, v___f_1328_);
lean_closure_set(v___f_1336_, 7, v___x_1333_);
lean_closure_set(v___f_1336_, 8, v_k_1260_);
lean_closure_set(v___f_1336_, 9, v___x_1327_);
lean_closure_set(v___f_1336_, 10, v___x_1306_);
lean_closure_set(v___f_1336_, 11, v_toMonadRef_1324_);
lean_closure_set(v___f_1336_, 12, v___x_1334_);
lean_closure_set(v___f_1336_, 13, v_numIndParams_1258_);
lean_closure_set(v___f_1336_, 14, v_a_1326_);
v___x_1379_ = lean_unbox(v_a_1330_);
lean_dec(v_a_1330_);
if (v___x_1379_ == 0)
{
v___y_1350_ = v_a_1261_;
v___y_1351_ = v_a_1262_;
v___y_1352_ = v_a_1263_;
v___y_1353_ = v_a_1264_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_6848__overap_1383_; lean_object* v___x_1384_; 
v___x_1380_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17);
lean_inc(v_a_1326_);
v___x_1381_ = l_Lean_MessageData_ofExpr(v_a_1326_);
v___x_1382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
lean_inc_ref(v_toMonadRef_1324_);
lean_inc_ref(v___x_1305_);
v___x_6848__overap_1383_ = l_Lean_addTrace___redArg(v___x_1305_, v___x_1306_, v_toMonadRef_1324_, v___x_1334_, v___x_1327_, v___x_1382_);
lean_inc(v_a_1264_);
lean_inc_ref(v_a_1263_);
lean_inc(v_a_1262_);
lean_inc_ref(v_a_1261_);
v___x_1384_ = lean_apply_5(v___x_6848__overap_1383_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, lean_box(0));
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_dec_ref_known(v___x_1384_, 1);
v___y_1350_ = v_a_1261_;
v___y_1351_ = v_a_1262_;
v___y_1352_ = v_a_1263_;
v___y_1353_ = v_a_1264_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v___f_1336_);
lean_dec(v_a_1326_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v_below_1257_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
v___jp_1337_:
{
lean_object* v_dummy_1342_; lean_object* v_nargs_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_6819__overap_1347_; lean_object* v___x_1348_; 
v_dummy_1342_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1343_ = l_Lean_Expr_getAppNumArgs(v_a_1326_);
lean_inc(v_nargs_1343_);
v___x_1344_ = lean_mk_array(v_nargs_1343_, v_dummy_1342_);
v___x_1345_ = lean_unsigned_to_nat(1u);
v___x_1346_ = lean_nat_sub(v_nargs_1343_, v___x_1345_);
lean_dec(v_nargs_1343_);
v___x_6819__overap_1347_ = l_Lean_Expr_withAppAux___redArg(v___f_1336_, v_a_1326_, v___x_1344_, v___x_1346_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
v___x_1348_ = lean_apply_5(v___x_6819__overap_1347_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, lean_box(0));
return v___x_1348_;
}
v___jp_1349_:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Meta_isTypeCorrect(v_below_1257_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; uint8_t v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = lean_unbox(v_a_1355_);
lean_dec(v_a_1355_);
if (v___x_1356_ == 0)
{
lean_object* v___x_1357_; lean_object* v_a_1358_; uint8_t v___x_1359_; 
v___x_1357_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1327_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref(v___x_1357_);
v___x_1359_ = lean_unbox(v_a_1358_);
lean_dec(v_a_1358_);
if (v___x_1359_ == 0)
{
lean_dec_ref(v___x_1305_);
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1352_;
v___y_1341_ = v___y_1353_;
goto v___jp_1337_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_6827__overap_1361_; lean_object* v___x_1362_; 
v___x_1360_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1324_);
v___x_6827__overap_1361_ = l_Lean_addTrace___redArg(v___x_1305_, v___x_1306_, v_toMonadRef_1324_, v___x_1334_, v___x_1327_, v___x_1360_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1362_ = lean_apply_5(v___x_6827__overap_1361_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_dec_ref_known(v___x_1362_, 1);
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1352_;
v___y_1341_ = v___y_1353_;
goto v___jp_1337_;
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v___f_1336_);
lean_dec(v_a_1326_);
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1305_);
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1352_;
v___y_1341_ = v___y_1353_;
goto v___jp_1337_;
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v___f_1336_);
lean_dec(v_a_1326_);
lean_dec_ref(v___x_1305_);
v_a_1371_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1354_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1354_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v___x_1322_);
lean_dec_ref(v___x_1305_);
lean_dec_ref(v_k_1260_);
lean_dec_ref(v_positions_1259_);
lean_dec(v_numIndParams_1258_);
lean_dec_ref(v_below_1257_);
v_a_1393_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1325_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1325_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1407_, lean_object* v_numIndParams_1408_, lean_object* v_positions_1409_, lean_object* v_k_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1407_, v_numIndParams_1408_, v_positions_1409_, v_k_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1417_, lean_object* v_inst_1418_, lean_object* v_below_1419_, lean_object* v_numIndParams_1420_, lean_object* v_positions_1421_, lean_object* v_k_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1419_, v_numIndParams_1420_, v_positions_1421_, v_k_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_inst_1430_, lean_object* v_below_1431_, lean_object* v_numIndParams_1432_, lean_object* v_positions_1433_, lean_object* v_k_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1429_, v_inst_1430_, v_below_1431_, v_numIndParams_1432_, v_positions_1433_, v_k_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_);
lean_dec(v_a_1438_);
lean_dec_ref(v_a_1437_);
lean_dec(v_a_1436_);
lean_dec_ref(v_a_1435_);
lean_dec(v_inst_1430_);
return v_res_1440_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = lean_unsigned_to_nat(32u);
v___x_1442_ = lean_mk_empty_array_with_capacity(v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1444_ = ((size_t)5ULL);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_unsigned_to_nat(32u);
v___x_1447_ = lean_mk_empty_array_with_capacity(v___x_1446_);
v___x_1448_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1449_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v___x_1447_);
lean_ctor_set(v___x_1449_, 2, v___x_1445_);
lean_ctor_set(v___x_1449_, 3, v___x_1445_);
lean_ctor_set_usize(v___x_1449_, 4, v___x_1444_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v_traceState_1453_; lean_object* v_traces_1454_; lean_object* v___x_1455_; lean_object* v_traceState_1456_; lean_object* v_env_1457_; lean_object* v_nextMacroScope_1458_; lean_object* v_ngen_1459_; lean_object* v_auxDeclNGen_1460_; lean_object* v_cache_1461_; lean_object* v_messages_1462_; lean_object* v_infoState_1463_; lean_object* v_snapshotTasks_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1483_; 
v___x_1452_ = lean_st_ref_get(v___y_1450_);
v_traceState_1453_ = lean_ctor_get(v___x_1452_, 4);
lean_inc_ref(v_traceState_1453_);
lean_dec(v___x_1452_);
v_traces_1454_ = lean_ctor_get(v_traceState_1453_, 0);
lean_inc_ref(v_traces_1454_);
lean_dec_ref(v_traceState_1453_);
v___x_1455_ = lean_st_ref_take(v___y_1450_);
v_traceState_1456_ = lean_ctor_get(v___x_1455_, 4);
v_env_1457_ = lean_ctor_get(v___x_1455_, 0);
v_nextMacroScope_1458_ = lean_ctor_get(v___x_1455_, 1);
v_ngen_1459_ = lean_ctor_get(v___x_1455_, 2);
v_auxDeclNGen_1460_ = lean_ctor_get(v___x_1455_, 3);
v_cache_1461_ = lean_ctor_get(v___x_1455_, 5);
v_messages_1462_ = lean_ctor_get(v___x_1455_, 6);
v_infoState_1463_ = lean_ctor_get(v___x_1455_, 7);
v_snapshotTasks_1464_ = lean_ctor_get(v___x_1455_, 8);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1466_ = v___x_1455_;
v_isShared_1467_ = v_isSharedCheck_1483_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_snapshotTasks_1464_);
lean_inc(v_infoState_1463_);
lean_inc(v_messages_1462_);
lean_inc(v_cache_1461_);
lean_inc(v_traceState_1456_);
lean_inc(v_auxDeclNGen_1460_);
lean_inc(v_ngen_1459_);
lean_inc(v_nextMacroScope_1458_);
lean_inc(v_env_1457_);
lean_dec(v___x_1455_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1483_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
uint64_t v_tid_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1481_; 
v_tid_1468_ = lean_ctor_get_uint64(v_traceState_1456_, sizeof(void*)*1);
v_isSharedCheck_1481_ = !lean_is_exclusive(v_traceState_1456_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_traceState_1456_, 0);
lean_dec(v_unused_1482_);
v___x_1470_ = v_traceState_1456_;
v_isShared_1471_ = v_isSharedCheck_1481_;
goto v_resetjp_1469_;
}
else
{
lean_dec(v_traceState_1456_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1481_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1472_);
lean_ctor_set_uint64(v_reuseFailAlloc_1480_, sizeof(void*)*1, v_tid_1468_);
v___x_1474_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 4, v___x_1474_);
v___x_1476_ = v___x_1466_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_env_1457_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_nextMacroScope_1458_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_ngen_1459_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_auxDeclNGen_1460_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v___x_1474_);
lean_ctor_set(v_reuseFailAlloc_1479_, 5, v_cache_1461_);
lean_ctor_set(v_reuseFailAlloc_1479_, 6, v_messages_1462_);
lean_ctor_set(v_reuseFailAlloc_1479_, 7, v_infoState_1463_);
lean_ctor_set(v_reuseFailAlloc_1479_, 8, v_snapshotTasks_1464_);
v___x_1476_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_st_ref_put(v___y_1450_, v___x_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v_traces_1454_);
return v___x_1478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1484_);
lean_dec(v___y_1484_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1498_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1499_, lean_object* v_opt_1500_){
_start:
{
lean_object* v_name_1501_; lean_object* v_defValue_1502_; lean_object* v_map_1503_; lean_object* v___x_1504_; 
v_name_1501_ = lean_ctor_get(v_opt_1500_, 0);
v_defValue_1502_ = lean_ctor_get(v_opt_1500_, 1);
v_map_1503_ = lean_ctor_get(v_opts_1499_, 0);
v___x_1504_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1503_, v_name_1501_);
if (lean_obj_tag(v___x_1504_) == 0)
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_unbox(v_defValue_1502_);
return v___x_1505_;
}
else
{
lean_object* v_val_1506_; 
v_val_1506_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1504_, 1);
if (lean_obj_tag(v_val_1506_) == 1)
{
uint8_t v_v_1507_; 
v_v_1507_ = lean_ctor_get_uint8(v_val_1506_, 0);
lean_dec_ref_known(v_val_1506_, 0);
return v_v_1507_;
}
else
{
uint8_t v___x_1508_; 
lean_dec(v_val_1506_);
v___x_1508_ = lean_unbox(v_defValue_1502_);
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1509_, lean_object* v_opt_1510_){
_start:
{
uint8_t v_res_1511_; lean_object* v_r_1512_; 
v_res_1511_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1509_, v_opt_1510_);
lean_dec_ref(v_opt_1510_);
lean_dec_ref(v_opts_1509_);
v_r_1512_ = lean_box(v_res_1511_);
return v_r_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1513_, lean_object* v_fnIndex_1514_, lean_object* v_recArg_1515_, lean_object* v_below_1516_, lean_object* v_Cs_1517_, lean_object* v_belowDict_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_array_get_borrowed(v___x_1513_, v_Cs_1517_, v_fnIndex_1514_);
lean_inc(v___x_1524_);
v___x_1525_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1524_, v_belowDict_1518_, v_recArg_1515_, v_below_1516_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1526_, lean_object* v_fnIndex_1527_, lean_object* v_recArg_1528_, lean_object* v_below_1529_, lean_object* v_Cs_1530_, lean_object* v_belowDict_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1526_, v_fnIndex_1527_, v_recArg_1528_, v_below_1529_, v_Cs_1530_, v_belowDict_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec_ref(v_Cs_1530_);
lean_dec(v_fnIndex_1527_);
lean_dec_ref(v___x_1526_);
return v_res_1537_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1543_ = l_Lean_stringToMessageData(v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1544_, lean_object* v_recArg_1545_, lean_object* v_x_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
lean_inc(v___y_1550_);
lean_inc_ref(v___y_1549_);
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
v___x_1552_ = lean_infer_type(v_below_1544_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1567_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1555_ = v___x_1552_;
v_isShared_1556_ = v_isSharedCheck_1567_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1552_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1567_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1557_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1558_ = l_Lean_MessageData_ofExpr(v_recArg_1545_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_MessageData_ofExpr(v_a_1553_);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v___x_1563_);
v___x_1565_ = v___x_1555_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_recArg_1545_);
v_a_1568_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1552_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1552_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1576_, lean_object* v_recArg_1577_, lean_object* v_x_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1576_, v_recArg_1577_, v_x_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
lean_dec(v___y_1582_);
lean_dec_ref(v___y_1581_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec_ref(v_x_1578_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1585_, size_t v_i_1586_, lean_object* v_bs_1587_){
_start:
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_usize_dec_lt(v_i_1586_, v_sz_1585_);
if (v___x_1588_ == 0)
{
return v_bs_1587_;
}
else
{
lean_object* v_v_1589_; lean_object* v_msg_1590_; lean_object* v___x_1591_; lean_object* v_bs_x27_1592_; size_t v___x_1593_; size_t v___x_1594_; lean_object* v___x_1595_; 
v_v_1589_ = lean_array_uget_borrowed(v_bs_1587_, v_i_1586_);
v_msg_1590_ = lean_ctor_get(v_v_1589_, 1);
lean_inc_ref(v_msg_1590_);
v___x_1591_ = lean_unsigned_to_nat(0u);
v_bs_x27_1592_ = lean_array_uset(v_bs_1587_, v_i_1586_, v___x_1591_);
v___x_1593_ = ((size_t)1ULL);
v___x_1594_ = lean_usize_add(v_i_1586_, v___x_1593_);
v___x_1595_ = lean_array_uset(v_bs_x27_1592_, v_i_1586_, v_msg_1590_);
v_i_1586_ = v___x_1594_;
v_bs_1587_ = v___x_1595_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1597_, lean_object* v_i_1598_, lean_object* v_bs_1599_){
_start:
{
size_t v_sz_boxed_1600_; size_t v_i_boxed_1601_; lean_object* v_res_1602_; 
v_sz_boxed_1600_ = lean_unbox_usize(v_sz_1597_);
lean_dec(v_sz_1597_);
v_i_boxed_1601_ = lean_unbox_usize(v_i_1598_);
lean_dec(v_i_1598_);
v_res_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_boxed_1600_, v_i_boxed_1601_, v_bs_1599_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1603_, lean_object* v_data_1604_, lean_object* v_ref_1605_, lean_object* v_msg_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v_toCold_1612_; lean_object* v_options_1613_; lean_object* v_currRecDepth_1614_; lean_object* v_maxRecDepth_1615_; lean_object* v_ref_1616_; lean_object* v_currNamespace_1617_; lean_object* v_openDecls_1618_; lean_object* v_initHeartbeats_1619_; lean_object* v_maxHeartbeats_1620_; lean_object* v_currMacroScope_1621_; uint8_t v_diag_1622_; uint8_t v_suppressElabErrors_1623_; lean_object* v___x_1624_; lean_object* v_traceState_1625_; lean_object* v_traces_1626_; lean_object* v_ref_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; size_t v_sz_1630_; size_t v___x_1631_; lean_object* v___x_1632_; lean_object* v_msg_1633_; lean_object* v___x_1634_; lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1672_; 
v_toCold_1612_ = lean_ctor_get(v___y_1609_, 0);
v_options_1613_ = lean_ctor_get(v___y_1609_, 1);
v_currRecDepth_1614_ = lean_ctor_get(v___y_1609_, 2);
v_maxRecDepth_1615_ = lean_ctor_get(v___y_1609_, 3);
v_ref_1616_ = lean_ctor_get(v___y_1609_, 4);
v_currNamespace_1617_ = lean_ctor_get(v___y_1609_, 5);
v_openDecls_1618_ = lean_ctor_get(v___y_1609_, 6);
v_initHeartbeats_1619_ = lean_ctor_get(v___y_1609_, 7);
v_maxHeartbeats_1620_ = lean_ctor_get(v___y_1609_, 8);
v_currMacroScope_1621_ = lean_ctor_get(v___y_1609_, 9);
v_diag_1622_ = lean_ctor_get_uint8(v___y_1609_, sizeof(void*)*10);
v_suppressElabErrors_1623_ = lean_ctor_get_uint8(v___y_1609_, sizeof(void*)*10 + 1);
v___x_1624_ = lean_st_ref_get(v___y_1610_);
v_traceState_1625_ = lean_ctor_get(v___x_1624_, 4);
lean_inc_ref(v_traceState_1625_);
lean_dec(v___x_1624_);
v_traces_1626_ = lean_ctor_get(v_traceState_1625_, 0);
lean_inc_ref(v_traces_1626_);
lean_dec_ref(v_traceState_1625_);
v_ref_1627_ = l_Lean_replaceRef(v_ref_1605_, v_ref_1616_);
lean_inc(v_currMacroScope_1621_);
lean_inc(v_maxHeartbeats_1620_);
lean_inc(v_initHeartbeats_1619_);
lean_inc(v_openDecls_1618_);
lean_inc(v_currNamespace_1617_);
lean_inc(v_maxRecDepth_1615_);
lean_inc(v_currRecDepth_1614_);
lean_inc_ref(v_options_1613_);
lean_inc_ref(v_toCold_1612_);
v___x_1628_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1628_, 0, v_toCold_1612_);
lean_ctor_set(v___x_1628_, 1, v_options_1613_);
lean_ctor_set(v___x_1628_, 2, v_currRecDepth_1614_);
lean_ctor_set(v___x_1628_, 3, v_maxRecDepth_1615_);
lean_ctor_set(v___x_1628_, 4, v_ref_1627_);
lean_ctor_set(v___x_1628_, 5, v_currNamespace_1617_);
lean_ctor_set(v___x_1628_, 6, v_openDecls_1618_);
lean_ctor_set(v___x_1628_, 7, v_initHeartbeats_1619_);
lean_ctor_set(v___x_1628_, 8, v_maxHeartbeats_1620_);
lean_ctor_set(v___x_1628_, 9, v_currMacroScope_1621_);
lean_ctor_set_uint8(v___x_1628_, sizeof(void*)*10, v_diag_1622_);
lean_ctor_set_uint8(v___x_1628_, sizeof(void*)*10 + 1, v_suppressElabErrors_1623_);
v___x_1629_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1626_);
lean_dec_ref(v_traces_1626_);
v_sz_1630_ = lean_array_size(v___x_1629_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1630_, v___x_1631_, v___x_1629_);
v_msg_1633_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1633_, 0, v_data_1604_);
lean_ctor_set(v_msg_1633_, 1, v_msg_1606_);
lean_ctor_set(v_msg_1633_, 2, v___x_1632_);
v___x_1634_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1633_, v___y_1607_, v___y_1608_, v___x_1628_, v___y_1610_);
lean_dec_ref_known(v___x_1628_, 10);
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
v___x_1639_ = lean_st_ref_take(v___y_1610_);
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
lean_ctor_set(v___x_1656_, 0, v_ref_1605_);
lean_ctor_set(v___x_1656_, 1, v_a_1635_);
v___x_1657_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1603_, v___x_1656_);
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
v___x_1662_ = lean_st_ref_put(v___y_1610_, v___x_1661_);
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
lean_inc(v___y_1746_);
v___x_1748_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1734_, v_data_1747_, v___y_1746_, v___y_1745_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
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
v___y_1745_ = v_a_1764_;
v___y_1746_ = v___y_1763_;
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
v___y_1745_ = v_a_1764_;
v___y_1746_ = v___y_1763_;
v_data_1747_ = v_data_1770_;
goto v___jp_1744_;
}
}
v___jp_1773_:
{
lean_object* v_ref_1774_; lean_object* v___x_1775_; 
v_ref_1774_ = lean_ctor_get(v___y_1739_, 4);
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
lean_object* v_options_1856_; lean_object* v_toCold_1857_; uint8_t v_hasTrace_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; 
v_options_1856_ = lean_ctor_get(v_a_1853_, 1);
v_toCold_1857_ = lean_ctor_get(v_a_1853_, 0);
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
lean_object* v_inheritedTraceOptions_1862_; lean_object* v___f_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v_a_1871_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v_a_1886_; 
v_inheritedTraceOptions_1862_ = lean_ctor_get(v_toCold_1857_, 4);
lean_inc_ref(v_below_1846_);
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1863_, 0, v_below_1846_);
lean_closure_set(v___f_1863_, 1, v_recArg_1850_);
v___x_1864_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1865_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1866_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1862_, v_options_1856_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1936_ = l_Lean_trace_profiler;
v___x_1937_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1856_, v___x_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; 
lean_dec_ref(v___f_1863_);
v___x_1938_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1846_, v_numIndParams_1847_, v_positions_1848_, v___f_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1938_;
}
else
{
goto v___jp_1895_;
}
}
else
{
goto v___jp_1895_;
}
v___jp_1868_:
{
lean_object* v___x_1872_; double v___x_1873_; double v___x_1874_; double v___x_1875_; double v___x_1876_; double v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1872_ = lean_io_mono_nanos_now();
v___x_1873_ = lean_float_of_nat(v___y_1870_);
v___x_1874_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__1, &l_Lean_Elab_Structural_toBelow___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___closed__1);
v___x_1875_ = lean_float_div(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_float_of_nat(v___x_1872_);
v___x_1877_ = lean_float_div(v___x_1876_, v___x_1874_);
v___x_1878_ = lean_box_float(v___x_1875_);
v___x_1879_ = lean_box_float(v___x_1877_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_a_1871_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1864_, v_hasTrace_1858_, v___x_1865_, v_options_1856_, v___x_1867_, v___y_1869_, v___f_1863_, v___x_1881_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1882_;
}
v___jp_1883_:
{
lean_object* v___x_1887_; double v___x_1888_; double v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1887_ = lean_io_get_num_heartbeats();
v___x_1888_ = lean_float_of_nat(v___y_1884_);
v___x_1889_ = lean_float_of_nat(v___x_1887_);
v___x_1890_ = lean_box_float(v___x_1888_);
v___x_1891_ = lean_box_float(v___x_1889_);
v___x_1892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v_a_1886_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1864_, v_hasTrace_1858_, v___x_1865_, v_options_1856_, v___x_1867_, v___y_1885_, v___f_1863_, v___x_1893_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
return v___x_1894_;
}
v___jp_1895_:
{
lean_object* v___x_1896_; lean_object* v_a_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1896_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1854_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1899_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1856_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_io_mono_nanos_now();
v___x_1901_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1846_, v_numIndParams_1847_, v_positions_1848_, v___f_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 1);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
v___y_1869_ = v_a_1897_;
v___y_1870_ = v___x_1900_;
v_a_1871_ = v___x_1907_;
goto v___jp_1868_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_a_1910_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1901_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1901_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 0);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
v___y_1869_ = v_a_1897_;
v___y_1870_ = v___x_1900_;
v_a_1871_ = v___x_1915_;
goto v___jp_1868_;
}
}
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_io_get_num_heartbeats();
v___x_1919_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1846_, v_numIndParams_1847_, v_positions_1848_, v___f_1860_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 1);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v___y_1884_ = v___x_1918_;
v___y_1885_ = v_a_1897_;
v_a_1886_ = v___x_1925_;
goto v___jp_1883_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set_tag(v___x_1930_, 0);
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
v___y_1884_ = v___x_1918_;
v___y_1885_ = v_a_1897_;
v_a_1886_ = v___x_1933_;
goto v___jp_1883_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1939_, lean_object* v_numIndParams_1940_, lean_object* v_positions_1941_, lean_object* v_fnIndex_1942_, lean_object* v_recArg_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_Elab_Structural_toBelow(v_below_1939_, v_numIndParams_1940_, v_positions_1941_, v_fnIndex_1942_, v_recArg_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1950_, lean_object* v_x_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1951_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1958_, lean_object* v_x_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1958_, v_x_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1966_, lean_object* v___y_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v___x_1974_; 
lean_inc(v___y_1972_);
lean_inc_ref(v___y_1971_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
lean_inc(v___y_1967_);
v___x_1974_ = lean_apply_7(v_k_1966_, v_b_1968_, v___y_1967_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, lean_box(0));
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_1975_, lean_object* v___y_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1975_, v___y_1976_, v_b_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1976_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_1984_, uint8_t v_bi_1985_, lean_object* v_type_1986_, lean_object* v_k_1987_, uint8_t v_kind_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___f_1995_; lean_object* v___x_1996_; 
lean_inc(v___y_1989_);
v___f_1995_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1995_, 0, v_k_1987_);
lean_closure_set(v___f_1995_, 1, v___y_1989_);
v___x_1996_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1984_, v_bi_1985_, v_type_1986_, v___f_1995_, v_kind_1988_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
if (lean_obj_tag(v___x_1996_) == 0)
{
return v___x_1996_;
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1996_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1996_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2005_, lean_object* v_bi_2006_, lean_object* v_type_2007_, lean_object* v_k_2008_, lean_object* v_kind_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v_bi_boxed_2016_; uint8_t v_kind_boxed_2017_; lean_object* v_res_2018_; 
v_bi_boxed_2016_ = lean_unbox(v_bi_2006_);
v_kind_boxed_2017_ = lean_unbox(v_kind_2009_);
v_res_2018_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2005_, v_bi_boxed_2016_, v_type_2007_, v_k_2008_, v_kind_boxed_2017_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2019_, lean_object* v_name_2020_, uint8_t v_bi_2021_, lean_object* v_type_2022_, lean_object* v_k_2023_, uint8_t v_kind_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2020_, v_bi_2021_, v_type_2022_, v_k_2023_, v_kind_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_name_2033_, lean_object* v_bi_2034_, lean_object* v_type_2035_, lean_object* v_k_2036_, lean_object* v_kind_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
uint8_t v_bi_boxed_2044_; uint8_t v_kind_boxed_2045_; lean_object* v_res_2046_; 
v_bi_boxed_2044_ = lean_unbox(v_bi_2034_);
v_kind_boxed_2045_ = lean_unbox(v_kind_2037_);
v_res_2046_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2032_, v_name_2033_, v_bi_boxed_2044_, v_type_2035_, v_k_2036_, v_kind_boxed_2045_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2047_, lean_object* v___y_2048_, lean_object* v_b_2049_, lean_object* v_c_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; 
lean_inc(v___y_2054_);
lean_inc_ref(v___y_2053_);
lean_inc(v___y_2052_);
lean_inc_ref(v___y_2051_);
lean_inc(v___y_2048_);
v___x_2056_ = lean_apply_8(v_k_2047_, v_b_2049_, v_c_2050_, v___y_2048_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, lean_box(0));
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2057_, lean_object* v___y_2058_, lean_object* v_b_2059_, lean_object* v_c_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2057_, v___y_2058_, v_b_2059_, v_c_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2058_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2067_, lean_object* v_maxFVars_2068_, lean_object* v_k_2069_, uint8_t v_cleanupAnnotations_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___f_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_inc(v___y_2071_);
v___f_2077_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2077_, 0, v_k_2069_);
lean_closure_set(v___f_2077_, 1, v___y_2071_);
v___x_2078_ = 1;
v___x_2079_ = 0;
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v_maxFVars_2068_);
v___x_2081_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2067_, v___x_2078_, v___x_2079_, v___x_2078_, v___x_2079_, v___x_2080_, v___f_2077_, v_cleanupAnnotations_2070_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
lean_dec_ref_known(v___x_2080_, 1);
if (lean_obj_tag(v___x_2081_) == 0)
{
return v___x_2081_;
}
else
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2089_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2089_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2090_, lean_object* v_maxFVars_2091_, lean_object* v_k_2092_, lean_object* v_cleanupAnnotations_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2100_; lean_object* v_res_2101_; 
v_cleanupAnnotations_boxed_2100_ = lean_unbox(v_cleanupAnnotations_2093_);
v_res_2101_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2090_, v_maxFVars_2091_, v_k_2092_, v_cleanupAnnotations_boxed_2100_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2102_, lean_object* v_e_2103_, lean_object* v_maxFVars_2104_, lean_object* v_k_2105_, uint8_t v_cleanupAnnotations_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2103_, v_maxFVars_2104_, v_k_2105_, v_cleanupAnnotations_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_e_2115_, lean_object* v_maxFVars_2116_, lean_object* v_k_2117_, lean_object* v_cleanupAnnotations_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2125_; lean_object* v_res_2126_; 
v_cleanupAnnotations_boxed_2125_ = lean_unbox(v_cleanupAnnotations_2118_);
v_res_2126_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2114_, v_e_2115_, v_maxFVars_2116_, v_k_2117_, v_cleanupAnnotations_boxed_2125_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_ref_2134_; lean_object* v___x_2135_; lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2180_; 
v_ref_2134_ = lean_ctor_get(v___y_2131_, 4);
v___x_2135_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2180_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2180_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v_traceState_2141_; lean_object* v_env_2142_; lean_object* v_nextMacroScope_2143_; lean_object* v_ngen_2144_; lean_object* v_auxDeclNGen_2145_; lean_object* v_cache_2146_; lean_object* v_messages_2147_; lean_object* v_infoState_2148_; lean_object* v_snapshotTasks_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2179_; 
v___x_2140_ = lean_st_ref_take(v___y_2132_);
v_traceState_2141_ = lean_ctor_get(v___x_2140_, 4);
v_env_2142_ = lean_ctor_get(v___x_2140_, 0);
v_nextMacroScope_2143_ = lean_ctor_get(v___x_2140_, 1);
v_ngen_2144_ = lean_ctor_get(v___x_2140_, 2);
v_auxDeclNGen_2145_ = lean_ctor_get(v___x_2140_, 3);
v_cache_2146_ = lean_ctor_get(v___x_2140_, 5);
v_messages_2147_ = lean_ctor_get(v___x_2140_, 6);
v_infoState_2148_ = lean_ctor_get(v___x_2140_, 7);
v_snapshotTasks_2149_ = lean_ctor_get(v___x_2140_, 8);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2151_ = v___x_2140_;
v_isShared_2152_ = v_isSharedCheck_2179_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_snapshotTasks_2149_);
lean_inc(v_infoState_2148_);
lean_inc(v_messages_2147_);
lean_inc(v_cache_2146_);
lean_inc(v_traceState_2141_);
lean_inc(v_auxDeclNGen_2145_);
lean_inc(v_ngen_2144_);
lean_inc(v_nextMacroScope_2143_);
lean_inc(v_env_2142_);
lean_dec(v___x_2140_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2179_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
uint64_t v_tid_2153_; lean_object* v_traces_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2178_; 
v_tid_2153_ = lean_ctor_get_uint64(v_traceState_2141_, sizeof(void*)*1);
v_traces_2154_ = lean_ctor_get(v_traceState_2141_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v_traceState_2141_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2156_ = v_traceState_2141_;
v_isShared_2157_ = v_isSharedCheck_2178_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_traces_2154_);
lean_dec(v_traceState_2141_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2178_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; double v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2158_ = lean_box(0);
v___x_2159_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2160_ = 0;
v___x_2161_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2162_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2162_, 0, v_cls_2127_);
lean_ctor_set(v___x_2162_, 1, v___x_2158_);
lean_ctor_set(v___x_2162_, 2, v___x_2161_);
lean_ctor_set_float(v___x_2162_, sizeof(void*)*3, v___x_2159_);
lean_ctor_set_float(v___x_2162_, sizeof(void*)*3 + 8, v___x_2159_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*3 + 16, v___x_2160_);
v___x_2163_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2164_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v_a_2136_);
lean_ctor_set(v___x_2164_, 2, v___x_2163_);
lean_inc(v_ref_2134_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_ref_2134_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_PersistentArray_push___redArg(v_traces_2154_, v___x_2165_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2166_);
v___x_2168_ = v___x_2156_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2166_);
lean_ctor_set_uint64(v_reuseFailAlloc_2177_, sizeof(void*)*1, v_tid_2153_);
v___x_2168_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
lean_object* v___x_2170_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 4, v___x_2168_);
v___x_2170_ = v___x_2151_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_env_2142_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_nextMacroScope_2143_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_ngen_2144_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_auxDeclNGen_2145_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v___x_2168_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_cache_2146_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_messages_2147_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_infoState_2148_);
lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_snapshotTasks_2149_);
v___x_2170_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2171_ = lean_st_ref_put(v___y_2132_, v___x_2170_);
v___x_2172_ = lean_box(0);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2172_);
v___x_2174_ = v___x_2138_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v___x_2172_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2181_, lean_object* v_msg_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2181_, v_msg_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2189_, lean_object* v_as_2190_, size_t v_i_2191_, size_t v_stop_2192_){
_start:
{
uint8_t v___x_2197_; 
v___x_2197_ = lean_usize_dec_eq(v_i_2191_, v_stop_2192_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; lean_object* v_fnName_2199_; lean_object* v_recArgPos_2200_; uint8_t v___x_2201_; 
v___x_2198_ = lean_array_uget_borrowed(v_as_2190_, v_i_2191_);
v_fnName_2199_ = lean_ctor_get(v___x_2198_, 0);
v_recArgPos_2200_ = lean_ctor_get(v___x_2198_, 2);
lean_inc(v_recArgPos_2200_);
lean_inc(v_fnName_2199_);
v___x_2201_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2199_, v_recArgPos_2200_, v_e_2189_);
if (v___x_2201_ == 0)
{
goto v___jp_2193_;
}
else
{
if (v___x_2201_ == 0)
{
goto v___jp_2193_;
}
else
{
return v___x_2201_;
}
}
}
else
{
uint8_t v___x_2202_; 
v___x_2202_ = 0;
return v___x_2202_;
}
v___jp_2193_:
{
size_t v___x_2194_; size_t v___x_2195_; 
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_add(v_i_2191_, v___x_2194_);
v_i_2191_ = v___x_2195_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2203_, lean_object* v_as_2204_, lean_object* v_i_2205_, lean_object* v_stop_2206_){
_start:
{
size_t v_i_boxed_2207_; size_t v_stop_boxed_2208_; uint8_t v_res_2209_; lean_object* v_r_2210_; 
v_i_boxed_2207_ = lean_unbox_usize(v_i_2205_);
lean_dec(v_i_2205_);
v_stop_boxed_2208_ = lean_unbox_usize(v_stop_2206_);
lean_dec(v_stop_2206_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2203_, v_as_2204_, v_i_boxed_2207_, v_stop_boxed_2208_);
lean_dec_ref(v_as_2204_);
lean_dec_ref(v_e_2203_);
v_r_2210_ = lean_box(v_res_2209_);
return v_r_2210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2211_, lean_object* v_____do__lift_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_options_2219_; uint8_t v_hasTrace_2220_; 
v_options_2219_ = lean_ctor_get(v___y_2216_, 1);
v_hasTrace_2220_ = lean_ctor_get_uint8(v_options_2219_, sizeof(void*)*1);
if (v_hasTrace_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_dec(v___x_2211_);
v___x_2221_ = lean_box(v_hasTrace_2220_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2224_ = l_Lean_Name_append(v___x_2223_, v___x_2211_);
v___x_2225_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2212_, v_options_2219_, v___x_2224_);
lean_dec(v___x_2224_);
v___x_2226_ = lean_box(v___x_2225_);
v___x_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2228_, lean_object* v_____do__lift_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2228_, v_____do__lift_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v_____do__lift_2229_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; lean_object* v_env_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2240_ = lean_st_ref_get(v___y_2238_);
v_env_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc_ref(v_env_2241_);
lean_dec(v___x_2240_);
v___x_2242_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2241_, v_declName_2237_);
v___x_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2243_, 0, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2244_, v___y_2245_);
lean_dec(v___y_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v_toApplicative_2256_; lean_object* v_toFunctor_2257_; lean_object* v_toSeq_2258_; lean_object* v_toSeqLeft_2259_; lean_object* v_toSeqRight_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___f_2266_; lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v_toApplicative_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2304_; 
v___x_2255_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2256_ = lean_ctor_get(v___x_2255_, 0);
v_toFunctor_2257_ = lean_ctor_get(v_toApplicative_2256_, 0);
v_toSeq_2258_ = lean_ctor_get(v_toApplicative_2256_, 2);
v_toSeqLeft_2259_ = lean_ctor_get(v_toApplicative_2256_, 3);
v_toSeqRight_2260_ = lean_ctor_get(v_toApplicative_2256_, 4);
v___f_2261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2257_, 2);
v___f_2263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2263_, 0, v_toFunctor_2257_);
v___f_2264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2264_, 0, v_toFunctor_2257_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___f_2263_);
lean_ctor_set(v___x_2265_, 1, v___f_2264_);
lean_inc(v_toSeqRight_2260_);
v___f_2266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2266_, 0, v_toSeqRight_2260_);
lean_inc(v_toSeqLeft_2259_);
v___f_2267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2267_, 0, v_toSeqLeft_2259_);
lean_inc(v_toSeq_2258_);
v___f_2268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2268_, 0, v_toSeq_2258_);
v___x_2269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2265_);
lean_ctor_set(v___x_2269_, 1, v___f_2261_);
lean_ctor_set(v___x_2269_, 2, v___f_2268_);
lean_ctor_set(v___x_2269_, 3, v___f_2267_);
lean_ctor_set(v___x_2269_, 4, v___f_2266_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
lean_ctor_set(v___x_2270_, 1, v___f_2262_);
v___x_2271_ = l_StateRefT_x27_instMonad___redArg(v___x_2270_);
v_toApplicative_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v___x_2271_, 1);
lean_dec(v_unused_2305_);
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2304_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_toApplicative_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2304_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v_toFunctor_2276_; lean_object* v_toSeq_2277_; lean_object* v_toSeqLeft_2278_; lean_object* v_toSeqRight_2279_; lean_object* v___x_2281_; uint8_t v_isShared_2282_; uint8_t v_isSharedCheck_2302_; 
v_toFunctor_2276_ = lean_ctor_get(v_toApplicative_2272_, 0);
v_toSeq_2277_ = lean_ctor_get(v_toApplicative_2272_, 2);
v_toSeqLeft_2278_ = lean_ctor_get(v_toApplicative_2272_, 3);
v_toSeqRight_2279_ = lean_ctor_get(v_toApplicative_2272_, 4);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_toApplicative_2272_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v_toApplicative_2272_, 1);
lean_dec(v_unused_2303_);
v___x_2281_ = v_toApplicative_2272_;
v_isShared_2282_ = v_isSharedCheck_2302_;
goto v_resetjp_2280_;
}
else
{
lean_inc(v_toSeqRight_2279_);
lean_inc(v_toSeqLeft_2278_);
lean_inc(v_toSeq_2277_);
lean_inc(v_toFunctor_2276_);
lean_dec(v_toApplicative_2272_);
v___x_2281_ = lean_box(0);
v_isShared_2282_ = v_isSharedCheck_2302_;
goto v_resetjp_2280_;
}
v_resetjp_2280_:
{
lean_object* v___f_2283_; lean_object* v___f_2284_; lean_object* v___f_2285_; lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___f_2290_; lean_object* v___x_2292_; 
v___f_2283_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2284_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2276_);
v___f_2285_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2285_, 0, v_toFunctor_2276_);
v___f_2286_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2286_, 0, v_toFunctor_2276_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___f_2285_);
lean_ctor_set(v___x_2287_, 1, v___f_2286_);
v___f_2288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2288_, 0, v_toSeqRight_2279_);
v___f_2289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2289_, 0, v_toSeqLeft_2278_);
v___f_2290_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2290_, 0, v_toSeq_2277_);
if (v_isShared_2282_ == 0)
{
lean_ctor_set(v___x_2281_, 4, v___f_2288_);
lean_ctor_set(v___x_2281_, 3, v___f_2289_);
lean_ctor_set(v___x_2281_, 2, v___f_2290_);
lean_ctor_set(v___x_2281_, 1, v___f_2283_);
lean_ctor_set(v___x_2281_, 0, v___x_2287_);
v___x_2292_ = v___x_2281_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___f_2283_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v___f_2290_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v___f_2289_);
lean_ctor_set(v_reuseFailAlloc_2301_, 4, v___f_2288_);
v___x_2292_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2294_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 1, v___f_2284_);
lean_ctor_set(v___x_2274_, 0, v___x_2292_);
v___x_2294_ = v___x_2274_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___f_2284_);
v___x_2294_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_23694__overap_2298_; lean_object* v___x_2299_; 
v___x_2295_ = l_StateRefT_x27_instMonad___redArg(v___x_2294_);
v___x_2296_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2297_ = l_instInhabitedOfMonad___redArg(v___x_2295_, v___x_2296_);
v___x_23694__overap_2298_ = lean_panic_fn_borrowed(v___x_2297_, v_msg_2248_);
lean_dec(v___x_2297_);
lean_inc(v___y_2253_);
lean_inc_ref(v___y_2252_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
v___x_2299_ = lean_apply_6(v___x_23694__overap_2298_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, lean_box(0));
return v___x_2299_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
return v_res_2313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2314_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_ctor_set(v___x_2319_, 2, v___x_2318_);
lean_ctor_set(v___x_2319_, 3, v___x_2318_);
lean_ctor_set(v___x_2319_, 4, v___x_2317_);
lean_ctor_set(v___x_2319_, 5, v___x_2317_);
lean_ctor_set(v___x_2319_, 6, v___x_2317_);
lean_ctor_set(v___x_2319_, 7, v___x_2317_);
lean_ctor_set(v___x_2319_, 8, v___x_2317_);
lean_ctor_set(v___x_2319_, 9, v___x_2317_);
lean_ctor_set(v___x_2319_, 10, v___x_2317_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = lean_unsigned_to_nat(32u);
v___x_2321_ = lean_mk_empty_array_with_capacity(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2323_ = ((size_t)5ULL);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_unsigned_to_nat(32u);
v___x_2326_ = lean_mk_empty_array_with_capacity(v___x_2325_);
v___x_2327_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
lean_ctor_set(v___x_2328_, 1, v___x_2326_);
lean_ctor_set(v___x_2328_, 2, v___x_2324_);
lean_ctor_set(v___x_2328_, 3, v___x_2324_);
lean_ctor_set_usize(v___x_2328_, 4, v___x_2323_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_box(1);
v___x_2330_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2331_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2330_);
lean_ctor_set(v___x_2332_, 2, v___x_2329_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2338_ = l_Lean_stringToMessageData(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2350_ = l_Lean_stringToMessageData(v___x_2349_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2353_ = l_Lean_stringToMessageData(v___x_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2354_, lean_object* v_declHint_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; lean_object* v_env_2359_; uint8_t v___x_2360_; 
v___x_2358_ = lean_st_ref_get(v___y_2356_);
v_env_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc_ref(v_env_2359_);
lean_dec(v___x_2358_);
v___x_2360_ = l_Lean_Name_isAnonymous(v_declHint_2355_);
if (v___x_2360_ == 0)
{
uint8_t v_isExporting_2361_; 
v_isExporting_2361_ = lean_ctor_get_uint8(v_env_2359_, sizeof(void*)*8);
if (v_isExporting_2361_ == 0)
{
lean_object* v___x_2362_; 
lean_dec_ref(v_env_2359_);
lean_dec(v_declHint_2355_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_msg_2354_);
return v___x_2362_;
}
else
{
lean_object* v___x_2363_; uint8_t v___x_2364_; 
lean_inc_ref(v_env_2359_);
v___x_2363_ = l_Lean_Environment_setExporting(v_env_2359_, v___x_2360_);
lean_inc(v_declHint_2355_);
lean_inc_ref(v___x_2363_);
v___x_2364_ = l_Lean_Environment_contains(v___x_2363_, v_declHint_2355_, v_isExporting_2361_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec_ref(v___x_2363_);
lean_dec_ref(v_env_2359_);
lean_dec(v_declHint_2355_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v_msg_2354_);
return v___x_2365_;
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_c_2371_; lean_object* v___x_2372_; 
v___x_2366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2368_ = l_Lean_Options_empty;
v___x_2369_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2363_);
lean_ctor_set(v___x_2369_, 1, v___x_2366_);
lean_ctor_set(v___x_2369_, 2, v___x_2367_);
lean_ctor_set(v___x_2369_, 3, v___x_2368_);
lean_inc(v_declHint_2355_);
v___x_2370_ = l_Lean_MessageData_ofConstName(v_declHint_2355_, v___x_2360_);
v_c_2371_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2371_, 0, v___x_2369_);
lean_ctor_set(v_c_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2359_, v_declHint_2355_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_dec_ref(v_env_2359_);
lean_dec(v_declHint_2355_);
v___x_2373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_c_2371_);
v___x_2375_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = l_Lean_MessageData_note(v___x_2376_);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_msg_2354_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2415_; 
v_val_2380_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2382_ = v___x_2372_;
v_isShared_2383_ = v_isSharedCheck_2415_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v___x_2372_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2415_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_mod_2387_; uint8_t v___x_2388_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = l_Lean_Environment_header(v_env_2359_);
lean_dec_ref(v_env_2359_);
v___x_2386_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2385_);
v_mod_2387_ = lean_array_get(v___x_2384_, v___x_2386_, v_val_2380_);
lean_dec(v_val_2380_);
lean_dec_ref(v___x_2386_);
v___x_2388_ = l_Lean_isPrivateName(v_declHint_2355_);
lean_dec(v_declHint_2355_);
if (v___x_2388_ == 0)
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2389_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v_c_2371_);
v___x_2391_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2390_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = l_Lean_MessageData_ofName(v_mod_2387_);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2392_);
lean_ctor_set(v___x_2394_, 1, v___x_2393_);
v___x_2395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_MessageData_note(v___x_2396_);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_msg_2354_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2398_);
v___x_2400_ = v___x_2382_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2413_; 
v___x_2402_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
lean_ctor_set(v___x_2403_, 1, v_c_2371_);
v___x_2404_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2403_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = l_Lean_MessageData_ofName(v_mod_2387_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = l_Lean_MessageData_note(v___x_2409_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_msg_2354_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2411_);
v___x_2413_ = v___x_2382_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2416_; 
lean_dec_ref(v_env_2359_);
lean_dec(v_declHint_2355_);
v___x_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_msg_2354_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2417_, lean_object* v_declHint_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2417_, v_declHint_2418_, v___y_2419_);
lean_dec(v___y_2419_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2422_, lean_object* v_declHint_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2440_; 
v___x_2430_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2422_, v_declHint_2423_, v___y_2428_);
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2440_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2440_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2435_ = l_Lean_unknownIdentifierMessageTag;
v___x_2436_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
lean_ctor_set(v___x_2436_, 1, v_a_2431_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v___x_2436_);
v___x_2438_ = v___x_2433_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2441_, lean_object* v_declHint_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2441_, v_declHint_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_ref_2456_; lean_object* v___x_2457_; lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2466_; 
v_ref_2456_ = lean_ctor_get(v___y_2453_, 4);
v___x_2457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2466_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v___x_2464_; 
lean_inc(v_ref_2456_);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_ref_2456_);
lean_ctor_set(v___x_2462_, 1, v_a_2458_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set_tag(v___x_2460_, 1);
lean_ctor_set(v___x_2460_, 0, v___x_2462_);
v___x_2464_ = v___x_2460_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v_res_2473_; 
v_res_2473_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
return v_res_2473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2474_, lean_object* v_msg_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_toCold_2482_; lean_object* v_options_2483_; lean_object* v_currRecDepth_2484_; lean_object* v_maxRecDepth_2485_; lean_object* v_ref_2486_; lean_object* v_currNamespace_2487_; lean_object* v_openDecls_2488_; lean_object* v_initHeartbeats_2489_; lean_object* v_maxHeartbeats_2490_; lean_object* v_currMacroScope_2491_; uint8_t v_diag_2492_; uint8_t v_suppressElabErrors_2493_; lean_object* v_ref_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_toCold_2482_ = lean_ctor_get(v___y_2479_, 0);
v_options_2483_ = lean_ctor_get(v___y_2479_, 1);
v_currRecDepth_2484_ = lean_ctor_get(v___y_2479_, 2);
v_maxRecDepth_2485_ = lean_ctor_get(v___y_2479_, 3);
v_ref_2486_ = lean_ctor_get(v___y_2479_, 4);
v_currNamespace_2487_ = lean_ctor_get(v___y_2479_, 5);
v_openDecls_2488_ = lean_ctor_get(v___y_2479_, 6);
v_initHeartbeats_2489_ = lean_ctor_get(v___y_2479_, 7);
v_maxHeartbeats_2490_ = lean_ctor_get(v___y_2479_, 8);
v_currMacroScope_2491_ = lean_ctor_get(v___y_2479_, 9);
v_diag_2492_ = lean_ctor_get_uint8(v___y_2479_, sizeof(void*)*10);
v_suppressElabErrors_2493_ = lean_ctor_get_uint8(v___y_2479_, sizeof(void*)*10 + 1);
v_ref_2494_ = l_Lean_replaceRef(v_ref_2474_, v_ref_2486_);
lean_inc(v_currMacroScope_2491_);
lean_inc(v_maxHeartbeats_2490_);
lean_inc(v_initHeartbeats_2489_);
lean_inc(v_openDecls_2488_);
lean_inc(v_currNamespace_2487_);
lean_inc(v_maxRecDepth_2485_);
lean_inc(v_currRecDepth_2484_);
lean_inc_ref(v_options_2483_);
lean_inc_ref(v_toCold_2482_);
v___x_2495_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2495_, 0, v_toCold_2482_);
lean_ctor_set(v___x_2495_, 1, v_options_2483_);
lean_ctor_set(v___x_2495_, 2, v_currRecDepth_2484_);
lean_ctor_set(v___x_2495_, 3, v_maxRecDepth_2485_);
lean_ctor_set(v___x_2495_, 4, v_ref_2494_);
lean_ctor_set(v___x_2495_, 5, v_currNamespace_2487_);
lean_ctor_set(v___x_2495_, 6, v_openDecls_2488_);
lean_ctor_set(v___x_2495_, 7, v_initHeartbeats_2489_);
lean_ctor_set(v___x_2495_, 8, v_maxHeartbeats_2490_);
lean_ctor_set(v___x_2495_, 9, v_currMacroScope_2491_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*10, v_diag_2492_);
lean_ctor_set_uint8(v___x_2495_, sizeof(void*)*10 + 1, v_suppressElabErrors_2493_);
v___x_2496_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2475_, v___y_2477_, v___y_2478_, v___x_2495_, v___y_2480_);
lean_dec_ref_known(v___x_2495_, 10);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2497_, lean_object* v_msg_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2497_, v_msg_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec(v_ref_2497_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2506_, lean_object* v_msg_2507_, lean_object* v_declHint_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; lean_object* v_a_2516_; lean_object* v___x_2517_; 
v___x_2515_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2507_, v_declHint_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2506_, v_a_2516_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2518_, lean_object* v_msg_2519_, lean_object* v_declHint_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2518_, v_msg_2519_, v_declHint_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec(v_ref_2518_);
return v_res_2527_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2530_ = l_Lean_stringToMessageData(v___x_2529_);
return v___x_2530_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2533_ = l_Lean_stringToMessageData(v___x_2532_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2534_, lean_object* v_constName_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
lean_object* v___x_2542_; uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2542_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2543_ = 0;
lean_inc(v_constName_2535_);
v___x_2544_ = l_Lean_MessageData_ofConstName(v_constName_2535_, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2542_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2545_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2534_, v___x_2547_, v_constName_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2549_, lean_object* v_constName_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2549_, v_constName_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec(v_ref_2549_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_){
_start:
{
lean_object* v_ref_2565_; lean_object* v___x_2566_; 
v_ref_2565_ = lean_ctor_get(v___y_2562_, 4);
v___x_2566_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2565_, v_constName_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; lean_object* v_env_2583_; uint8_t v___x_2584_; lean_object* v___x_2585_; 
v___x_2582_ = lean_st_ref_get(v___y_2580_);
v_env_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc_ref(v_env_2583_);
lean_dec(v___x_2582_);
v___x_2584_ = 0;
lean_inc(v_constName_2575_);
v___x_2585_ = l_Lean_Environment_find_x3f(v_env_2583_, v_constName_2575_, v___x_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2586_;
}
else
{
lean_object* v_val_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_constName_2575_);
v_val_2587_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2585_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_val_2587_);
lean_dec(v___x_2585_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 0);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_val_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
return v_res_2602_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2606_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2607_ = lean_unsigned_to_nat(53u);
v___x_2608_ = lean_unsigned_to_nat(62u);
v___x_2609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2611_ = l_mkPanicMessageWithDecl(v___x_2610_, v___x_2609_, v___x_2608_, v___x_2607_, v___x_2606_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2612_, size_t v_i_2613_, lean_object* v_bs_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v___x_2621_; 
v___x_2621_ = lean_usize_dec_lt(v_i_2613_, v_sz_2612_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2622_, 0, v_bs_2614_);
return v___x_2622_;
}
else
{
lean_object* v_v_2623_; lean_object* v___x_2624_; 
v_v_2623_ = lean_array_uget_borrowed(v_bs_2614_, v_i_2613_);
lean_inc(v_v_2623_);
v___x_2624_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2623_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2626_; lean_object* v_bs_x27_2627_; lean_object* v_a_2629_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = lean_unsigned_to_nat(0u);
v_bs_x27_2627_ = lean_array_uset(v_bs_2614_, v_i_2613_, v___x_2626_);
if (lean_obj_tag(v_a_2625_) == 6)
{
lean_object* v_val_2634_; lean_object* v_numFields_2635_; uint8_t v___x_2636_; lean_object* v___x_2637_; 
v_val_2634_ = lean_ctor_get(v_a_2625_, 0);
lean_inc_ref(v_val_2634_);
lean_dec_ref_known(v_a_2625_, 1);
v_numFields_2635_ = lean_ctor_get(v_val_2634_, 4);
lean_inc(v_numFields_2635_);
lean_dec_ref(v_val_2634_);
v___x_2636_ = 0;
v___x_2637_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2637_, 0, v_numFields_2635_);
lean_ctor_set(v___x_2637_, 1, v___x_2626_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*2, v___x_2636_);
v_a_2629_ = v___x_2637_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec(v_a_2625_);
v___x_2638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2639_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2638_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref_known(v___x_2639_, 1);
v_a_2629_ = v_a_2640_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec_ref(v_bs_x27_2627_);
v_a_2641_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2639_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2639_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
v___jp_2628_:
{
size_t v___x_2630_; size_t v___x_2631_; lean_object* v___x_2632_; 
v___x_2630_ = ((size_t)1ULL);
v___x_2631_ = lean_usize_add(v_i_2613_, v___x_2630_);
v___x_2632_ = lean_array_uset(v_bs_x27_2627_, v_i_2613_, v_a_2629_);
v_i_2613_ = v___x_2631_;
v_bs_2614_ = v___x_2632_;
goto _start;
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v_bs_2614_);
v_a_2649_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2624_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2624_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2657_, lean_object* v_i_2658_, lean_object* v_bs_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
size_t v_sz_boxed_2666_; size_t v_i_boxed_2667_; lean_object* v_res_2668_; 
v_sz_boxed_2666_ = lean_unbox_usize(v_sz_2657_);
lean_dec(v_sz_2657_);
v_i_boxed_2667_ = lean_unbox_usize(v_i_2658_);
lean_dec(v_i_2658_);
v_res_2668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2666_, v_i_boxed_2667_, v_bs_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
return v_res_2668_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = lean_box(0);
v___x_2670_ = lean_unsigned_to_nat(16u);
v___x_2671_ = lean_mk_array(v___x_2670_, v___x_2669_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
lean_ctor_set(v___x_2674_, 1, v___x_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2677_, uint8_t v_alsoCasesOn_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v___x_2688_; 
v___x_2688_ = l_Lean_Expr_isApp(v_e_2677_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_dec_ref(v_e_2677_);
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
return v___x_2690_;
}
else
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_Expr_getAppFn(v_e_2677_);
if (lean_obj_tag(v___x_2691_) == 4)
{
lean_object* v_declName_2692_; lean_object* v_us_2693_; lean_object* v___x_2694_; lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2848_; 
v_declName_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc_n(v_declName_2692_, 2);
v_us_2693_ = lean_ctor_get(v___x_2691_, 1);
lean_inc(v_us_2693_);
lean_dec_ref_known(v___x_2691_, 2);
v___x_2694_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2692_, v___y_2683_);
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2848_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2848_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2699_; 
v___x_2699_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_2695_) == 1)
{
lean_object* v_val_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2741_; 
v_val_2700_ = lean_ctor_get(v_a_2695_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v_a_2695_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2702_ = v_a_2695_;
v_isShared_2703_ = v_isSharedCheck_2741_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_val_2700_);
lean_dec(v_a_2695_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2741_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v_dummy_2704_; lean_object* v_nargs_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v_args_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; 
v_dummy_2704_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2705_ = l_Lean_Expr_getAppNumArgs(v_e_2677_);
lean_inc(v_nargs_2705_);
v___x_2706_ = lean_mk_array(v_nargs_2705_, v_dummy_2704_);
v___x_2707_ = lean_unsigned_to_nat(1u);
v___x_2708_ = lean_nat_sub(v_nargs_2705_, v___x_2707_);
lean_dec(v_nargs_2705_);
v_args_2709_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2677_, v___x_2706_, v___x_2708_);
v___x_2710_ = lean_array_get_size(v_args_2709_);
v___x_2711_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2700_);
v___x_2712_ = lean_nat_dec_lt(v___x_2710_, v___x_2711_);
lean_dec(v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v_numParams_2713_; lean_object* v_numDiscrs_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v_numParams_2713_ = lean_ctor_get(v_val_2700_, 0);
v_numDiscrs_2714_ = lean_ctor_get(v_val_2700_, 1);
v___x_2715_ = lean_array_mk(v_us_2693_);
v___x_2716_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2713_);
v___x_2717_ = l_Array_extract___redArg(v_args_2709_, v___x_2716_, v_numParams_2713_);
v___x_2718_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2700_);
v___x_2719_ = lean_array_get(v___x_2699_, v_args_2709_, v___x_2718_);
lean_dec(v___x_2718_);
v___x_2720_ = lean_nat_add(v_numParams_2713_, v___x_2707_);
v___x_2721_ = lean_nat_add(v___x_2720_, v_numDiscrs_2714_);
lean_inc(v___x_2721_);
lean_inc_ref_n(v_args_2709_, 2);
v___x_2722_ = l_Array_toSubarray___redArg(v_args_2709_, v___x_2720_, v___x_2721_);
v___x_2723_ = l_Subarray_copy___redArg(v___x_2722_);
v___x_2724_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2700_);
v___x_2725_ = lean_nat_add(v___x_2721_, v___x_2724_);
lean_dec(v___x_2724_);
lean_inc(v___x_2725_);
v___x_2726_ = l_Array_toSubarray___redArg(v_args_2709_, v___x_2721_, v___x_2725_);
v___x_2727_ = l_Subarray_copy___redArg(v___x_2726_);
v___x_2728_ = l_Array_toSubarray___redArg(v_args_2709_, v___x_2725_, v___x_2710_);
v___x_2729_ = l_Subarray_copy___redArg(v___x_2728_);
v___x_2730_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2730_, 0, v_val_2700_);
lean_ctor_set(v___x_2730_, 1, v_declName_2692_);
lean_ctor_set(v___x_2730_, 2, v___x_2715_);
lean_ctor_set(v___x_2730_, 3, v___x_2717_);
lean_ctor_set(v___x_2730_, 4, v___x_2719_);
lean_ctor_set(v___x_2730_, 5, v___x_2723_);
lean_ctor_set(v___x_2730_, 6, v___x_2727_);
lean_ctor_set(v___x_2730_, 7, v___x_2729_);
if (v_isShared_2703_ == 0)
{
lean_ctor_set(v___x_2702_, 0, v___x_2730_);
v___x_2732_ = v___x_2702_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2734_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2732_);
v___x_2734_ = v___x_2697_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
else
{
lean_object* v___x_2737_; lean_object* v___x_2739_; 
lean_dec_ref(v_args_2709_);
lean_del_object(v___x_2702_);
lean_dec(v_val_2700_);
lean_dec(v_us_2693_);
lean_dec(v_declName_2692_);
v___x_2737_ = lean_box(0);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 0, v___x_2737_);
v___x_2739_ = v___x_2697_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v___x_2742_; 
lean_del_object(v___x_2697_);
lean_dec(v_a_2695_);
v___x_2742_ = lean_st_ref_get(v___y_2683_);
if (v_alsoCasesOn_2678_ == 0)
{
lean_dec(v___x_2742_);
lean_dec(v_us_2693_);
lean_dec(v_declName_2692_);
lean_dec_ref(v_e_2677_);
goto v___jp_2685_;
}
else
{
lean_object* v_env_2743_; uint8_t v___x_2744_; 
v_env_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc_ref(v_env_2743_);
lean_dec(v___x_2742_);
lean_inc(v_declName_2692_);
v___x_2744_ = l_Lean_isCasesOnRecursor(v_env_2743_, v_declName_2692_);
if (v___x_2744_ == 0)
{
lean_dec(v_us_2693_);
lean_dec(v_declName_2692_);
lean_dec_ref(v_e_2677_);
goto v___jp_2685_;
}
else
{
lean_object* v_indName_2745_; lean_object* v___x_2746_; 
v_indName_2745_ = l_Lean_Name_getPrefix(v_declName_2692_);
v___x_2746_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2745_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2839_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2839_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2839_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
if (lean_obj_tag(v_a_2747_) == 5)
{
lean_object* v_val_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2834_; 
v_val_2751_ = lean_ctor_get(v_a_2747_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v_a_2747_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2753_ = v_a_2747_;
v_isShared_2754_ = v_isSharedCheck_2834_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_val_2751_);
lean_dec(v_a_2747_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2834_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v_toConstantVal_2755_; lean_object* v_numParams_2756_; lean_object* v_numIndices_2757_; lean_object* v_ctors_2758_; lean_object* v_nargs_2759_; lean_object* v_dummy_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v_args_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_toConstantVal_2755_ = lean_ctor_get(v_val_2751_, 0);
lean_inc_ref(v_toConstantVal_2755_);
v_numParams_2756_ = lean_ctor_get(v_val_2751_, 1);
lean_inc(v_numParams_2756_);
v_numIndices_2757_ = lean_ctor_get(v_val_2751_, 2);
lean_inc(v_numIndices_2757_);
v_ctors_2758_ = lean_ctor_get(v_val_2751_, 4);
lean_inc(v_ctors_2758_);
v_nargs_2759_ = l_Lean_Expr_getAppNumArgs(v_e_2677_);
v_dummy_2760_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2759_);
v___x_2761_ = lean_mk_array(v_nargs_2759_, v_dummy_2760_);
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_nat_sub(v_nargs_2759_, v___x_2762_);
lean_dec(v_nargs_2759_);
v_args_2764_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2677_, v___x_2761_, v___x_2763_);
v___x_2765_ = lean_nat_add(v_numParams_2756_, v___x_2762_);
v___x_2766_ = lean_nat_add(v___x_2765_, v_numIndices_2757_);
v___x_2767_ = lean_nat_add(v___x_2766_, v___x_2762_);
lean_dec(v___x_2766_);
v___x_2768_ = l_Lean_InductiveVal_numCtors(v_val_2751_);
lean_dec_ref(v_val_2751_);
v___x_2769_ = lean_nat_add(v___x_2767_, v___x_2768_);
lean_dec(v___x_2768_);
v___x_2770_ = lean_array_get_size(v_args_2764_);
v___x_2771_ = lean_nat_dec_le(v___x_2769_, v___x_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v___x_2769_);
lean_dec(v___x_2767_);
lean_dec(v___x_2765_);
lean_dec_ref(v_args_2764_);
lean_dec(v_ctors_2758_);
lean_dec(v_numIndices_2757_);
lean_dec(v_numParams_2756_);
lean_dec_ref(v_toConstantVal_2755_);
lean_del_object(v___x_2753_);
lean_dec(v_us_2693_);
lean_dec(v_declName_2692_);
v___x_2772_ = lean_box(0);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2772_);
v___x_2774_ = v___x_2749_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
else
{
lean_object* v___x_2776_; lean_object* v_params_2777_; lean_object* v_motive_2778_; lean_object* v_discrs_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_discrInfos_2782_; lean_object* v_alts_2783_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v_lower_2825_; lean_object* v_upper_2826_; uint8_t v___x_2833_; 
lean_del_object(v___x_2749_);
v___x_2776_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2756_);
lean_inc_ref_n(v_args_2764_, 3);
v_params_2777_ = l_Array_toSubarray___redArg(v_args_2764_, v___x_2776_, v_numParams_2756_);
v_motive_2778_ = lean_array_get(v___x_2699_, v_args_2764_, v_numParams_2756_);
lean_dec(v_numParams_2756_);
lean_inc(v___x_2767_);
v_discrs_2779_ = l_Array_toSubarray___redArg(v_args_2764_, v___x_2765_, v___x_2767_);
v___x_2780_ = lean_nat_add(v_numIndices_2757_, v___x_2762_);
lean_dec(v_numIndices_2757_);
v___x_2781_ = lean_box(0);
v_discrInfos_2782_ = lean_mk_array(v___x_2780_, v___x_2781_);
lean_inc(v___x_2769_);
v_alts_2783_ = l_Array_toSubarray___redArg(v_args_2764_, v___x_2767_, v___x_2769_);
v___x_2833_ = lean_nat_dec_le(v___x_2769_, v___x_2776_);
if (v___x_2833_ == 0)
{
v_lower_2825_ = v___x_2769_;
v_upper_2826_ = v___x_2770_;
goto v___jp_2824_;
}
else
{
lean_dec(v___x_2769_);
v_lower_2825_ = v___x_2776_;
v_upper_2826_ = v___x_2770_;
goto v___jp_2824_;
}
v___jp_2784_:
{
lean_object* v___x_2787_; size_t v_sz_2788_; size_t v___x_2789_; lean_object* v___x_2790_; 
v___x_2787_ = lean_array_mk(v_ctors_2758_);
v_sz_2788_ = lean_array_size(v___x_2787_);
v___x_2789_ = ((size_t)0ULL);
v___x_2790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2788_, v___x_2789_, v___x_2787_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2815_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2815_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2815_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v_start_2795_; lean_object* v_stop_2796_; lean_object* v_start_2797_; lean_object* v_stop_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v_start_2795_ = lean_ctor_get(v_params_2777_, 1);
lean_inc(v_start_2795_);
v_stop_2796_ = lean_ctor_get(v_params_2777_, 2);
lean_inc(v_stop_2796_);
v_start_2797_ = lean_ctor_get(v_discrs_2779_, 1);
lean_inc(v_start_2797_);
v_stop_2798_ = lean_ctor_get(v_discrs_2779_, 2);
lean_inc(v_stop_2798_);
v___x_2799_ = lean_nat_sub(v_stop_2796_, v_start_2795_);
lean_dec(v_start_2795_);
lean_dec(v_stop_2796_);
v___x_2800_ = lean_nat_sub(v_stop_2798_, v_start_2797_);
lean_dec(v_start_2797_);
lean_dec(v_stop_2798_);
v___x_2801_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2802_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2799_);
lean_ctor_set(v___x_2802_, 1, v___x_2800_);
lean_ctor_set(v___x_2802_, 2, v_a_2791_);
lean_ctor_set(v___x_2802_, 3, v___y_2786_);
lean_ctor_set(v___x_2802_, 4, v_discrInfos_2782_);
lean_ctor_set(v___x_2802_, 5, v___x_2801_);
v___x_2803_ = lean_array_mk(v_us_2693_);
v___x_2804_ = l_Subarray_copy___redArg(v_params_2777_);
v___x_2805_ = l_Subarray_copy___redArg(v_discrs_2779_);
v___x_2806_ = l_Subarray_copy___redArg(v_alts_2783_);
v___x_2807_ = l_Subarray_copy___redArg(v___y_2785_);
v___x_2808_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2802_);
lean_ctor_set(v___x_2808_, 1, v_declName_2692_);
lean_ctor_set(v___x_2808_, 2, v___x_2803_);
lean_ctor_set(v___x_2808_, 3, v___x_2804_);
lean_ctor_set(v___x_2808_, 4, v_motive_2778_);
lean_ctor_set(v___x_2808_, 5, v___x_2805_);
lean_ctor_set(v___x_2808_, 6, v___x_2806_);
lean_ctor_set(v___x_2808_, 7, v___x_2807_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 1);
lean_ctor_set(v___x_2753_, 0, v___x_2808_);
v___x_2810_ = v___x_2753_;
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
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2810_);
v___x_2812_ = v___x_2793_;
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
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec_ref(v_alts_2783_);
lean_dec_ref(v_discrInfos_2782_);
lean_dec_ref(v_discrs_2779_);
lean_dec(v_motive_2778_);
lean_dec_ref(v_params_2777_);
lean_del_object(v___x_2753_);
lean_dec(v_us_2693_);
lean_dec(v_declName_2692_);
v_a_2816_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2790_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2790_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
v___jp_2824_:
{
lean_object* v_levelParams_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v_levelParams_2827_ = lean_ctor_get(v_toConstantVal_2755_, 1);
lean_inc(v_levelParams_2827_);
lean_dec_ref(v_toConstantVal_2755_);
v___x_2828_ = l_Array_toSubarray___redArg(v_args_2764_, v_lower_2825_, v_upper_2826_);
v___x_2829_ = l_List_lengthTR___redArg(v_levelParams_2827_);
lean_dec(v_levelParams_2827_);
v___x_2830_ = l_List_lengthTR___redArg(v_us_2693_);
v___x_2831_ = lean_nat_dec_eq(v___x_2829_, v___x_2830_);
lean_dec(v___x_2830_);
lean_dec(v___x_2829_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; 
v___x_2832_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2785_ = v___x_2828_;
v___y_2786_ = v___x_2832_;
goto v___jp_2784_;
}
else
{
v___y_2785_ = v___x_2828_;
v___y_2786_ = v___x_2781_;
goto v___jp_2784_;
}
}
}
}
}
else
{
lean_object* v___x_2835_; lean_object* v___x_2837_; 
lean_dec(v_a_2747_);
lean_dec(v_us_2693_);
lean_dec(v_declName_2692_);
lean_dec_ref(v_e_2677_);
v___x_2835_ = lean_box(0);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2835_);
v___x_2837_ = v___x_2749_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2835_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_dec(v_us_2693_);
lean_dec(v_declName_2692_);
lean_dec_ref(v_e_2677_);
v_a_2840_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2746_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2746_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
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
lean_dec_ref(v___x_2691_);
lean_dec_ref(v_e_2677_);
goto v___jp_2685_;
}
}
v___jp_2685_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2849_, lean_object* v_alsoCasesOn_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2857_; lean_object* v_res_2858_; 
v_alsoCasesOn_boxed_2857_ = lean_unbox(v_alsoCasesOn_2850_);
v_res_2858_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2849_, v_alsoCasesOn_boxed_2857_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
if (lean_obj_tag(v_a_2859_) == 0)
{
lean_object* v___x_2861_; 
v___x_2861_ = l_List_reverse___redArg(v_a_2860_);
return v___x_2861_;
}
else
{
lean_object* v_head_2862_; lean_object* v_tail_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2872_; 
v_head_2862_ = lean_ctor_get(v_a_2859_, 0);
v_tail_2863_ = lean_ctor_get(v_a_2859_, 1);
v_isSharedCheck_2872_ = !lean_is_exclusive(v_a_2859_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2865_ = v_a_2859_;
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_tail_2863_);
lean_inc(v_head_2862_);
lean_dec(v_a_2859_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2872_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = l_Lean_MessageData_ofExpr(v_head_2862_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 1, v_a_2860_);
lean_ctor_set(v___x_2865_, 0, v___x_2867_);
v___x_2869_ = v___x_2865_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_a_2860_);
v___x_2869_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
v_a_2859_ = v_tail_2863_;
v_a_2860_ = v___x_2869_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2873_, lean_object* v_x_2874_){
_start:
{
lean_object* v_fnName_2875_; uint8_t v___x_2876_; 
v_fnName_2875_ = lean_ctor_get(v_x_2874_, 0);
v___x_2876_ = l_Lean_Expr_isConstOf(v_x_2873_, v_fnName_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2877_, lean_object* v_x_2878_){
_start:
{
uint8_t v_res_2879_; lean_object* v_r_2880_; 
v_res_2879_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2877_, v_x_2878_);
lean_dec_ref(v_x_2878_);
lean_dec_ref(v_x_2877_);
v_r_2880_ = lean_box(v_res_2879_);
return v_r_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2881_, lean_object* v_type_2882_, lean_object* v_val_2883_, lean_object* v_k_2884_, uint8_t v_nondep_2885_, uint8_t v_kind_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___f_2893_; lean_object* v___x_2894_; 
lean_inc(v___y_2887_);
v___f_2893_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2893_, 0, v_k_2884_);
lean_closure_set(v___f_2893_, 1, v___y_2887_);
v___x_2894_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2881_, v_type_2882_, v_val_2883_, v___f_2893_, v_nondep_2885_, v_kind_2886_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2894_) == 0)
{
return v___x_2894_;
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2903_, lean_object* v_type_2904_, lean_object* v_val_2905_, lean_object* v_k_2906_, lean_object* v_nondep_2907_, lean_object* v_kind_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v_nondep_boxed_2915_; uint8_t v_kind_boxed_2916_; lean_object* v_res_2917_; 
v_nondep_boxed_2915_ = lean_unbox(v_nondep_2907_);
v_kind_boxed_2916_ = lean_unbox(v_kind_2908_);
v_res_2917_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2903_, v_type_2904_, v_val_2905_, v_k_2906_, v_nondep_boxed_2915_, v_kind_boxed_2916_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2918_, uint8_t v_usedLetOnly_2919_, lean_object* v_x_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v___x_2927_; 
lean_inc(v___y_2925_);
lean_inc_ref(v___y_2924_);
lean_inc(v___y_2923_);
lean_inc_ref(v___y_2922_);
lean_inc(v___y_2921_);
lean_inc_ref(v_x_2920_);
v___x_2927_ = lean_apply_7(v_k_2918_, v_x_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, lean_box(0));
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; uint8_t v___x_2933_; lean_object* v___x_2934_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
v___x_2929_ = lean_unsigned_to_nat(1u);
v___x_2930_ = lean_mk_empty_array_with_capacity(v___x_2929_);
v___x_2931_ = lean_array_push(v___x_2930_, v_x_2920_);
v___x_2932_ = 0;
v___x_2933_ = 1;
v___x_2934_ = l_Lean_Meta_mkLetFVars(v___x_2931_, v_a_2928_, v_usedLetOnly_2919_, v___x_2932_, v___x_2933_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec_ref(v___x_2931_);
return v___x_2934_;
}
else
{
lean_dec_ref(v_x_2920_);
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2935_, lean_object* v_usedLetOnly_2936_, lean_object* v_x_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
uint8_t v_usedLetOnly_boxed_2944_; lean_object* v_res_2945_; 
v_usedLetOnly_boxed_2944_ = lean_unbox(v_usedLetOnly_2936_);
v_res_2945_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2935_, v_usedLetOnly_boxed_2944_, v_x_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2946_, lean_object* v_type_2947_, lean_object* v_val_2948_, lean_object* v_k_2949_, uint8_t v_nondep_2950_, uint8_t v_kind_2951_, uint8_t v_usedLetOnly_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_box(v_usedLetOnly_2952_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2960_, 0, v_k_2949_);
lean_closure_set(v___f_2960_, 1, v___x_2959_);
v___x_2961_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2946_, v_type_2947_, v_val_2948_, v___f_2960_, v_nondep_2950_, v_kind_2951_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2962_, lean_object* v_type_2963_, lean_object* v_val_2964_, lean_object* v_k_2965_, lean_object* v_nondep_2966_, lean_object* v_kind_2967_, lean_object* v_usedLetOnly_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
uint8_t v_nondep_boxed_2975_; uint8_t v_kind_boxed_2976_; uint8_t v_usedLetOnly_boxed_2977_; lean_object* v_res_2978_; 
v_nondep_boxed_2975_ = lean_unbox(v_nondep_2966_);
v_kind_boxed_2976_ = lean_unbox(v_kind_2967_);
v_usedLetOnly_boxed_2977_ = lean_unbox(v_usedLetOnly_2968_);
v_res_2978_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2962_, v_type_2963_, v_val_2964_, v_k_2965_, v_nondep_boxed_2975_, v_kind_boxed_2976_, v_usedLetOnly_boxed_2977_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_2979_, lean_object* v_positions_2980_, lean_object* v_recFnNames_2981_, lean_object* v_containsRecFn_2982_, lean_object* v_below_2983_, size_t v_sz_2984_, size_t v_i_2985_, lean_object* v_bs_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
uint8_t v___x_2993_; 
v___x_2993_ = lean_usize_dec_lt(v_i_2985_, v_sz_2984_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; 
lean_dec_ref(v_below_2983_);
lean_dec_ref(v_containsRecFn_2982_);
lean_dec_ref(v_recFnNames_2981_);
lean_dec_ref(v_positions_2980_);
lean_dec_ref(v_recArgInfos_2979_);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_bs_2986_);
return v___x_2994_;
}
else
{
lean_object* v_v_2995_; lean_object* v___x_2996_; 
v_v_2995_ = lean_array_uget_borrowed(v_bs_2986_, v_i_2985_);
lean_inc_ref(v___y_2990_);
lean_inc(v_v_2995_);
lean_inc_ref(v_below_2983_);
lean_inc_ref(v_containsRecFn_2982_);
lean_inc_ref(v_recFnNames_2981_);
lean_inc_ref(v_positions_2980_);
lean_inc_ref(v_recArgInfos_2979_);
v___x_2996_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2979_, v_positions_2980_, v_recFnNames_2981_, v_containsRecFn_2982_, v_below_2983_, v_v_2995_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2998_; lean_object* v_bs_x27_2999_; size_t v___x_3000_; size_t v___x_3001_; lean_object* v___x_3002_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
v___x_2998_ = lean_unsigned_to_nat(0u);
v_bs_x27_2999_ = lean_array_uset(v_bs_2986_, v_i_2985_, v___x_2998_);
v___x_3000_ = ((size_t)1ULL);
v___x_3001_ = lean_usize_add(v_i_2985_, v___x_3000_);
v___x_3002_ = lean_array_uset(v_bs_x27_2999_, v_i_2985_, v_a_2997_);
v_i_2985_ = v___x_3001_;
v_bs_2986_ = v___x_3002_;
goto _start;
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec_ref(v_bs_2986_);
lean_dec_ref(v_below_2983_);
lean_dec_ref(v_containsRecFn_2982_);
lean_dec_ref(v_recFnNames_2981_);
lean_dec_ref(v_positions_2980_);
lean_dec_ref(v_recArgInfos_2979_);
v_a_3004_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2996_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2996_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3014_ = l_Lean_stringToMessageData(v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3017_ = l_Lean_stringToMessageData(v___x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3018_, lean_object* v_positions_3019_, lean_object* v_recFnNames_3020_, lean_object* v_containsRecFn_3021_, lean_object* v_below_3022_, lean_object* v_e_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_, lean_object* v_x_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
if (lean_obj_tag(v_x_3024_) == 5)
{
lean_object* v_fn_3033_; lean_object* v_arg_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_fn_3033_ = lean_ctor_get(v_x_3024_, 0);
lean_inc_ref(v_fn_3033_);
v_arg_3034_ = lean_ctor_get(v_x_3024_, 1);
lean_inc_ref(v_arg_3034_);
lean_dec_ref_known(v_x_3024_, 2);
v___x_3035_ = lean_array_set(v_x_3025_, v_x_3026_, v_arg_3034_);
v___x_3036_ = lean_unsigned_to_nat(1u);
v___x_3037_ = lean_nat_sub(v_x_3026_, v___x_3036_);
lean_dec(v_x_3026_);
v_x_3024_ = v_fn_3033_;
v_x_3025_ = v___x_3035_;
v_x_3026_ = v___x_3037_;
goto _start;
}
else
{
lean_object* v___f_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec(v_x_3026_);
lean_inc_ref(v_x_3024_);
v___f_3039_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3039_, 0, v_x_3024_);
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3039_, v_recArgInfos_3018_, v___x_3040_);
if (lean_obj_tag(v___x_3041_) == 1)
{
lean_object* v_val_3042_; lean_object* v___x_3043_; lean_object* v___y_3045_; lean_object* v_recArgPos_3071_; lean_object* v_indGroupInst_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
lean_dec_ref(v_x_3024_);
v_val_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_val_3042_);
lean_dec_ref_known(v___x_3041_, 1);
v___x_3043_ = lean_array_fget_borrowed(v_recArgInfos_3018_, v_val_3042_);
v_recArgPos_3071_ = lean_ctor_get(v___x_3043_, 2);
v_indGroupInst_3072_ = lean_ctor_get(v___x_3043_, 4);
v___x_3073_ = lean_array_get_size(v_x_3025_);
v___x_3074_ = lean_nat_dec_lt(v_recArgPos_3071_, v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec(v_val_3042_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_below_3022_);
lean_dec_ref(v_containsRecFn_3021_);
lean_dec_ref(v_recFnNames_3020_);
lean_dec_ref(v_positions_3019_);
lean_dec_ref(v_recArgInfos_3018_);
v___x_3075_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3076_ = l_Lean_indentExpr(v_e_3023_);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
v___x_3078_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3077_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3078_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_array_fget_borrowed(v_x_3025_, v_recArgPos_3071_);
lean_inc_ref(v___y_3030_);
lean_inc(v___x_3079_);
lean_inc_ref(v_below_3022_);
lean_inc_ref(v_containsRecFn_3021_);
lean_inc_ref(v_recFnNames_3020_);
lean_inc_ref(v_positions_3019_);
lean_inc_ref(v_recArgInfos_3018_);
v___x_3080_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3018_, v_positions_3019_, v_recFnNames_3020_, v_containsRecFn_3021_, v_below_3022_, v___x_3079_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v_params_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v_params_3082_ = lean_ctor_get(v_indGroupInst_3072_, 2);
v___x_3083_ = lean_array_get_size(v_params_3082_);
lean_inc_ref(v_positions_3019_);
lean_inc_ref(v_below_3022_);
v___x_3084_ = l_Lean_Elab_Structural_toBelow(v_below_3022_, v___x_3083_, v_positions_3019_, v_val_3042_, v_a_3081_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_dec_ref(v_e_3023_);
v___y_3045_ = v___x_3084_;
goto v___jp_3044_;
}
else
{
lean_object* v_a_3085_; uint8_t v___y_3087_; uint8_t v___x_3092_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
v___x_3092_ = l_Lean_Exception_isInterrupt(v_a_3085_);
if (v___x_3092_ == 0)
{
uint8_t v___x_3093_; 
v___x_3093_ = l_Lean_Exception_isRuntime(v_a_3085_);
v___y_3087_ = v___x_3093_;
goto v___jp_3086_;
}
else
{
lean_dec(v_a_3085_);
v___y_3087_ = v___x_3092_;
goto v___jp_3086_;
}
v___jp_3086_:
{
if (v___y_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref_known(v___x_3084_, 1);
v___x_3088_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3089_ = l_Lean_indentExpr(v_e_3023_);
v___x_3090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3090_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
v___y_3045_ = v___x_3091_;
goto v___jp_3044_;
}
else
{
lean_dec_ref(v_e_3023_);
v___y_3045_ = v___x_3084_;
goto v___jp_3044_;
}
}
}
}
else
{
lean_dec(v_val_3042_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_e_3023_);
lean_dec_ref(v_below_3022_);
lean_dec_ref(v_containsRecFn_3021_);
lean_dec_ref(v_recFnNames_3020_);
lean_dec_ref(v_positions_3019_);
lean_dec_ref(v_recArgInfos_3018_);
return v___x_3080_;
}
}
v___jp_3044_:
{
if (lean_obj_tag(v___y_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v_fixedParamPerm_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v_snd_3050_; size_t v_sz_3051_; size_t v___x_3052_; lean_object* v___x_3053_; 
v_a_3046_ = lean_ctor_get(v___y_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___y_3045_, 1);
v_fixedParamPerm_3047_ = lean_ctor_get(v___x_3043_, 1);
v___x_3048_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3047_, v_x_3025_);
lean_dec_ref(v_x_3025_);
lean_inc(v___x_3043_);
v___x_3049_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3043_, v___x_3048_);
v_snd_3050_ = lean_ctor_get(v___x_3049_, 1);
lean_inc(v_snd_3050_);
lean_dec_ref(v___x_3049_);
v_sz_3051_ = lean_array_size(v_snd_3050_);
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3018_, v_positions_3019_, v_recFnNames_3020_, v_containsRecFn_3021_, v_below_3022_, v_sz_3051_, v___x_3052_, v_snd_3050_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3062_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3056_ = v___x_3053_;
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3058_ = l_Lean_mkAppN(v_a_3046_, v_a_3054_);
lean_dec(v_a_3054_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3058_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_a_3046_);
v_a_3063_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3053_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3053_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
else
{
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_below_3022_);
lean_dec_ref(v_containsRecFn_3021_);
lean_dec_ref(v_recFnNames_3020_);
lean_dec_ref(v_positions_3019_);
lean_dec_ref(v_recArgInfos_3018_);
return v___y_3045_;
}
}
}
else
{
lean_object* v___x_3094_; 
lean_dec(v___x_3041_);
lean_dec_ref(v_e_3023_);
lean_inc_ref(v___y_3030_);
lean_inc_ref(v_below_3022_);
lean_inc_ref(v_containsRecFn_3021_);
lean_inc_ref(v_recFnNames_3020_);
lean_inc_ref(v_positions_3019_);
lean_inc_ref(v_recArgInfos_3018_);
v___x_3094_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3018_, v_positions_3019_, v_recFnNames_3020_, v_containsRecFn_3021_, v_below_3022_, v_x_3024_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; size_t v_sz_3096_; size_t v___x_3097_; lean_object* v___x_3098_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3094_, 1);
v_sz_3096_ = lean_array_size(v_x_3025_);
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3018_, v_positions_3019_, v_recFnNames_3020_, v_containsRecFn_3021_, v_below_3022_, v_sz_3096_, v___x_3097_, v_x_3025_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3107_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3101_ = v___x_3098_;
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3098_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = l_Lean_mkAppN(v_a_3095_, v_a_3099_);
lean_dec(v_a_3099_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3105_ = v___x_3101_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3095_);
v_a_3108_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3098_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3098_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_below_3022_);
lean_dec_ref(v_containsRecFn_3021_);
lean_dec_ref(v_recFnNames_3020_);
lean_dec_ref(v_positions_3019_);
lean_dec_ref(v_recArgInfos_3018_);
return v___x_3094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3116_, lean_object* v_recArgInfos_3117_, lean_object* v_positions_3118_, lean_object* v_recFnNames_3119_, lean_object* v_containsRecFn_3120_, lean_object* v_below_3121_, uint8_t v___x_3122_, uint8_t v_a_3123_, lean_object* v_x_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_expr_instantiate1(v_body_3116_, v_x_3124_);
lean_inc_ref(v___y_3128_);
v___x_3132_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3117_, v_positions_3118_, v_recFnNames_3119_, v_containsRecFn_3120_, v_below_3121_, v___x_3131_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v___x_3134_ = lean_unsigned_to_nat(1u);
v___x_3135_ = lean_mk_empty_array_with_capacity(v___x_3134_);
v___x_3136_ = lean_array_push(v___x_3135_, v_x_3124_);
v___x_3137_ = 1;
v___x_3138_ = l_Lean_Meta_mkLambdaFVars(v___x_3136_, v_a_3133_, v___x_3122_, v_a_3123_, v___x_3122_, v_a_3123_, v___x_3137_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec_ref(v___x_3136_);
return v___x_3138_;
}
else
{
lean_dec_ref(v_x_3124_);
return v___x_3132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3139_, lean_object* v_recArgInfos_3140_, lean_object* v_positions_3141_, lean_object* v_recFnNames_3142_, lean_object* v_containsRecFn_3143_, lean_object* v_below_3144_, lean_object* v___x_3145_, lean_object* v_a_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
uint8_t v___x_28810__boxed_3154_; uint8_t v_a_28811__boxed_3155_; lean_object* v_res_3156_; 
v___x_28810__boxed_3154_ = lean_unbox(v___x_3145_);
v_a_28811__boxed_3155_ = lean_unbox(v_a_3146_);
v_res_3156_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3139_, v_recArgInfos_3140_, v_positions_3141_, v_recFnNames_3142_, v_containsRecFn_3143_, v_below_3144_, v___x_28810__boxed_3154_, v_a_28811__boxed_3155_, v_x_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v_body_3139_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3157_, lean_object* v_recArgInfos_3158_, lean_object* v_positions_3159_, lean_object* v_recFnNames_3160_, lean_object* v_containsRecFn_3161_, lean_object* v_below_3162_, uint8_t v___x_3163_, uint8_t v_a_3164_, lean_object* v_x_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_expr_instantiate1(v_body_3157_, v_x_3165_);
lean_inc_ref(v___y_3169_);
v___x_3173_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3158_, v_positions_3159_, v_recFnNames_3160_, v_containsRecFn_3161_, v_below_3162_, v___x_3172_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref_known(v___x_3173_, 1);
v___x_3175_ = lean_unsigned_to_nat(1u);
v___x_3176_ = lean_mk_empty_array_with_capacity(v___x_3175_);
v___x_3177_ = lean_array_push(v___x_3176_, v_x_3165_);
v___x_3178_ = 1;
v___x_3179_ = l_Lean_Meta_mkForallFVars(v___x_3177_, v_a_3174_, v___x_3163_, v_a_3164_, v_a_3164_, v___x_3178_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec_ref(v___x_3177_);
return v___x_3179_;
}
else
{
lean_dec_ref(v_x_3165_);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3180_, lean_object* v_recArgInfos_3181_, lean_object* v_positions_3182_, lean_object* v_recFnNames_3183_, lean_object* v_containsRecFn_3184_, lean_object* v_below_3185_, lean_object* v___x_3186_, lean_object* v_a_3187_, lean_object* v_x_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
uint8_t v___x_28828__boxed_3195_; uint8_t v_a_28829__boxed_3196_; lean_object* v_res_3197_; 
v___x_28828__boxed_3195_ = lean_unbox(v___x_3186_);
v_a_28829__boxed_3196_ = lean_unbox(v_a_3187_);
v_res_3197_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3180_, v_recArgInfos_3181_, v_positions_3182_, v_recFnNames_3183_, v_containsRecFn_3184_, v_below_3185_, v___x_28828__boxed_3195_, v_a_28829__boxed_3196_, v_x_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v_body_3180_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3198_, lean_object* v_recArgInfos_3199_, lean_object* v_positions_3200_, lean_object* v_recFnNames_3201_, lean_object* v_containsRecFn_3202_, lean_object* v_below_3203_, lean_object* v_x_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3198_, v_recArgInfos_3199_, v_positions_3200_, v_recFnNames_3201_, v_containsRecFn_3202_, v_below_3203_, v_x_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v_x_3204_);
lean_dec_ref(v_body_3198_);
return v_res_3211_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3216_ = l_Lean_stringToMessageData(v___x_3215_);
return v___x_3216_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3219_ = l_Lean_stringToMessageData(v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3226_, lean_object* v_b_3227_, lean_object* v_recArgInfos_3228_, lean_object* v_positions_3229_, lean_object* v_recFnNames_3230_, lean_object* v_containsRecFn_3231_, uint8_t v___x_3232_, uint8_t v_a_3233_, lean_object* v___x_3234_, lean_object* v_a_3235_, lean_object* v_e_3236_, lean_object* v___x_3237_, lean_object* v_xs_3238_, lean_object* v_altBody_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v_options_3281_; uint8_t v_hasTrace_3282_; 
v_options_3281_ = lean_ctor_get(v___y_3243_, 1);
v_hasTrace_3282_ = lean_ctor_get_uint8(v_options_3281_, sizeof(void*)*1);
if (v_hasTrace_3282_ == 0)
{
lean_dec(v___x_3237_);
v___y_3258_ = v___y_3240_;
v___y_3259_ = v___y_3241_;
v___y_3260_ = v___y_3242_;
v___y_3261_ = v___y_3243_;
v___y_3262_ = v___y_3244_;
goto v___jp_3257_;
}
else
{
lean_object* v_toCold_3283_; lean_object* v_inheritedTraceOptions_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; 
v_toCold_3283_ = lean_ctor_get(v___y_3243_, 0);
v_inheritedTraceOptions_3284_ = lean_ctor_get(v_toCold_3283_, 4);
v___x_3285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3237_);
v___x_3286_ = l_Lean_Name_append(v___x_3285_, v___x_3237_);
v___x_3287_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3284_, v_options_3281_, v___x_3286_);
lean_dec(v___x_3286_);
if (v___x_3287_ == 0)
{
lean_dec(v___x_3237_);
v___y_3258_ = v___y_3240_;
v___y_3259_ = v___y_3241_;
v___y_3260_ = v___y_3242_;
v___y_3261_ = v___y_3243_;
v___y_3262_ = v___y_3244_;
goto v___jp_3257_;
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3288_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3227_);
v___x_3289_ = l_Nat_reprFast(v_b_3227_);
v___x_3290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3290_, 0, v___x_3289_);
v___x_3291_ = l_Lean_MessageData_ofFormat(v___x_3290_);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3288_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
lean_inc_ref(v_xs_3238_);
v___x_3295_ = lean_array_to_list(v_xs_3238_);
v___x_3296_ = lean_box(0);
v___x_3297_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3295_, v___x_3296_);
v___x_3298_ = l_Lean_MessageData_ofList(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3294_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3237_, v___x_3299_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_dec_ref_known(v___x_3300_, 1);
v___y_3258_ = v___y_3240_;
v___y_3259_ = v___y_3241_;
v___y_3260_ = v___y_3242_;
v___y_3261_ = v___y_3243_;
v___y_3262_ = v___y_3244_;
goto v___jp_3257_;
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_altBody_3239_);
lean_dec_ref(v_xs_3238_);
lean_dec_ref(v_e_3236_);
lean_dec_ref(v_a_3235_);
lean_dec_ref(v_containsRecFn_3231_);
lean_dec_ref(v_recFnNames_3230_);
lean_dec_ref(v_positions_3229_);
lean_dec_ref(v_recArgInfos_3228_);
lean_dec(v_b_3227_);
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
v___jp_3246_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = lean_array_get_borrowed(v___x_3226_, v_xs_3238_, v_b_3227_);
lean_dec(v_b_3227_);
lean_inc_ref(v___y_3250_);
lean_inc(v___x_3252_);
v___x_3253_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3228_, v_positions_3229_, v_recFnNames_3230_, v_containsRecFn_3231_, v___x_3252_, v_altBody_3239_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref_known(v___x_3253_, 1);
v___x_3255_ = 1;
v___x_3256_ = l_Lean_Meta_mkLambdaFVars(v_xs_3238_, v_a_3254_, v___x_3232_, v_a_3233_, v___x_3232_, v_a_3233_, v___x_3255_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref(v_xs_3238_);
return v___x_3256_;
}
else
{
lean_dec_ref(v_xs_3238_);
return v___x_3253_;
}
}
v___jp_3257_:
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = lean_array_get_size(v_xs_3238_);
v___x_3264_ = lean_nat_dec_eq(v___x_3263_, v___x_3234_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec_ref(v_altBody_3239_);
lean_dec_ref(v_xs_3238_);
lean_dec_ref(v_containsRecFn_3231_);
lean_dec_ref(v_recFnNames_3230_);
lean_dec_ref(v_positions_3229_);
lean_dec_ref(v_recArgInfos_3228_);
lean_dec(v_b_3227_);
v___x_3265_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3266_ = l_Lean_indentExpr(v_a_3235_);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3269_, 0, v___x_3267_);
lean_ctor_set(v___x_3269_, 1, v___x_3268_);
v___x_3270_ = l_Lean_indentExpr(v_e_3236_);
v___x_3271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3271_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
else
{
lean_dec_ref(v_e_3236_);
lean_dec_ref(v_a_3235_);
v___y_3247_ = v___y_3258_;
v___y_3248_ = v___y_3259_;
v___y_3249_ = v___y_3260_;
v___y_3250_ = v___y_3261_;
v___y_3251_ = v___y_3262_;
goto v___jp_3246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3309_ = _args[0];
lean_object* v_b_3310_ = _args[1];
lean_object* v_recArgInfos_3311_ = _args[2];
lean_object* v_positions_3312_ = _args[3];
lean_object* v_recFnNames_3313_ = _args[4];
lean_object* v_containsRecFn_3314_ = _args[5];
lean_object* v___x_3315_ = _args[6];
lean_object* v_a_3316_ = _args[7];
lean_object* v___x_3317_ = _args[8];
lean_object* v_a_3318_ = _args[9];
lean_object* v_e_3319_ = _args[10];
lean_object* v___x_3320_ = _args[11];
lean_object* v_xs_3321_ = _args[12];
lean_object* v_altBody_3322_ = _args[13];
lean_object* v___y_3323_ = _args[14];
lean_object* v___y_3324_ = _args[15];
lean_object* v___y_3325_ = _args[16];
lean_object* v___y_3326_ = _args[17];
lean_object* v___y_3327_ = _args[18];
lean_object* v___y_3328_ = _args[19];
_start:
{
uint8_t v___x_28904__boxed_3329_; uint8_t v_a_28905__boxed_3330_; lean_object* v_res_3331_; 
v___x_28904__boxed_3329_ = lean_unbox(v___x_3315_);
v_a_28905__boxed_3330_ = lean_unbox(v_a_3316_);
v_res_3331_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3309_, v_b_3310_, v_recArgInfos_3311_, v_positions_3312_, v_recFnNames_3313_, v_containsRecFn_3314_, v___x_28904__boxed_3329_, v_a_28905__boxed_3330_, v___x_3317_, v_a_3318_, v_e_3319_, v___x_3320_, v_xs_3321_, v_altBody_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec(v___x_3317_);
lean_dec_ref(v___x_3309_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3332_, lean_object* v_positions_3333_, lean_object* v_recFnNames_3334_, lean_object* v_containsRecFn_3335_, uint8_t v_a_3336_, lean_object* v_e_3337_, lean_object* v_as_3338_, lean_object* v_bs_3339_, lean_object* v_i_3340_, lean_object* v_cs_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3348_ = lean_array_get_size(v_as_3338_);
v___x_3349_ = lean_nat_dec_lt(v_i_3340_, v___x_3348_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
lean_dec(v_i_3340_);
lean_dec_ref(v_e_3337_);
lean_dec_ref(v_containsRecFn_3335_);
lean_dec_ref(v_recFnNames_3334_);
lean_dec_ref(v_positions_3333_);
lean_dec_ref(v_recArgInfos_3332_);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_cs_3341_);
return v___x_3350_;
}
else
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = lean_array_get_size(v_bs_3339_);
v___x_3352_ = lean_nat_dec_lt(v_i_3340_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; 
lean_dec(v_i_3340_);
lean_dec_ref(v_e_3337_);
lean_dec_ref(v_containsRecFn_3335_);
lean_dec_ref(v_recFnNames_3334_);
lean_dec_ref(v_positions_3333_);
lean_dec_ref(v_recArgInfos_3332_);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_cs_3341_);
return v___x_3353_;
}
else
{
lean_object* v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v_a_3357_; lean_object* v_b_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___f_3363_; lean_object* v___x_3364_; 
v___x_3354_ = l_Lean_instInhabitedExpr;
v___x_3355_ = 0;
v___x_3356_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3357_ = lean_array_fget_borrowed(v_as_3338_, v_i_3340_);
v_b_3358_ = lean_array_fget_borrowed(v_bs_3339_, v_i_3340_);
v___x_3359_ = lean_unsigned_to_nat(1u);
v___x_3360_ = lean_nat_add(v_b_3358_, v___x_3359_);
v___x_3361_ = lean_box(v___x_3355_);
v___x_3362_ = lean_box(v_a_3336_);
lean_inc_ref(v_e_3337_);
lean_inc_n(v_a_3357_, 2);
lean_inc(v___x_3360_);
lean_inc_ref(v_containsRecFn_3335_);
lean_inc_ref(v_recFnNames_3334_);
lean_inc_ref(v_positions_3333_);
lean_inc_ref(v_recArgInfos_3332_);
lean_inc(v_b_3358_);
v___f_3363_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3363_, 0, v___x_3354_);
lean_closure_set(v___f_3363_, 1, v_b_3358_);
lean_closure_set(v___f_3363_, 2, v_recArgInfos_3332_);
lean_closure_set(v___f_3363_, 3, v_positions_3333_);
lean_closure_set(v___f_3363_, 4, v_recFnNames_3334_);
lean_closure_set(v___f_3363_, 5, v_containsRecFn_3335_);
lean_closure_set(v___f_3363_, 6, v___x_3361_);
lean_closure_set(v___f_3363_, 7, v___x_3362_);
lean_closure_set(v___f_3363_, 8, v___x_3360_);
lean_closure_set(v___f_3363_, 9, v_a_3357_);
lean_closure_set(v___f_3363_, 10, v_e_3337_);
lean_closure_set(v___f_3363_, 11, v___x_3356_);
v___x_3364_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3357_, v___x_3360_, v___f_3363_, v___x_3355_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref_known(v___x_3364_, 1);
v___x_3366_ = lean_nat_add(v_i_3340_, v___x_3359_);
lean_dec(v_i_3340_);
v___x_3367_ = lean_array_push(v_cs_3341_, v_a_3365_);
v_i_3340_ = v___x_3366_;
v_cs_3341_ = v___x_3367_;
goto _start;
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec_ref(v_cs_3341_);
lean_dec(v_i_3340_);
lean_dec_ref(v_e_3337_);
lean_dec_ref(v_containsRecFn_3335_);
lean_dec_ref(v_recFnNames_3334_);
lean_dec_ref(v_positions_3333_);
lean_dec_ref(v_recArgInfos_3332_);
v_a_3369_ = lean_ctor_get(v___x_3364_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3364_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3364_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3364_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
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
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3379_ = l_Lean_stringToMessageData(v___x_3378_);
return v___x_3379_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3382_ = l_Lean_stringToMessageData(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3385_ = l_Lean_stringToMessageData(v___x_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3386_, lean_object* v_positions_3387_, lean_object* v_recFnNames_3388_, lean_object* v_containsRecFn_3389_, lean_object* v_below_3390_, lean_object* v_e_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_e_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___x_3411_; 
lean_inc_ref(v_containsRecFn_3389_);
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc(v_a_3394_);
lean_inc_ref(v_a_3393_);
lean_inc(v_a_3392_);
lean_inc_ref(v_e_3391_);
v___x_3411_ = lean_apply_7(v_containsRecFn_3389_, v_e_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, lean_box(0));
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3632_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3414_ = v___x_3411_;
v_isShared_3415_ = v_isSharedCheck_3632_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3411_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3632_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
uint8_t v___x_3416_; 
v___x_3416_ = lean_unbox(v_a_3412_);
if (v___x_3416_ == 0)
{
lean_object* v___x_3418_; 
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
if (v_isShared_3415_ == 0)
{
lean_ctor_set(v___x_3414_, 0, v_e_3391_);
v___x_3418_ = v___x_3414_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_e_3391_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
else
{
uint8_t v___x_3420_; 
lean_del_object(v___x_3414_);
v___x_3420_ = 0;
switch(lean_obj_tag(v_e_3391_))
{
case 6:
{
lean_object* v_binderName_3421_; lean_object* v_binderType_3422_; lean_object* v_body_3423_; uint8_t v_binderInfo_3424_; lean_object* v___x_3425_; 
v_binderName_3421_ = lean_ctor_get(v_e_3391_, 0);
lean_inc(v_binderName_3421_);
v_binderType_3422_ = lean_ctor_get(v_e_3391_, 1);
lean_inc_ref(v_binderType_3422_);
v_body_3423_ = lean_ctor_get(v_e_3391_, 2);
lean_inc_ref(v_body_3423_);
v_binderInfo_3424_ = lean_ctor_get_uint8(v_e_3391_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3391_, 3);
lean_inc_ref(v_a_3395_);
lean_inc_ref(v_below_3390_);
lean_inc_ref(v_containsRecFn_3389_);
lean_inc_ref(v_recFnNames_3388_);
lean_inc_ref(v_positions_3387_);
lean_inc_ref(v_recArgInfos_3386_);
v___x_3425_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v_below_3390_, v_binderType_3422_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; lean_object* v___f_3428_; uint8_t v___x_3429_; lean_object* v___x_3430_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref_known(v___x_3425_, 1);
v___x_3427_ = lean_box(v___x_3420_);
v___f_3428_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3428_, 0, v_body_3423_);
lean_closure_set(v___f_3428_, 1, v_recArgInfos_3386_);
lean_closure_set(v___f_3428_, 2, v_positions_3387_);
lean_closure_set(v___f_3428_, 3, v_recFnNames_3388_);
lean_closure_set(v___f_3428_, 4, v_containsRecFn_3389_);
lean_closure_set(v___f_3428_, 5, v_below_3390_);
lean_closure_set(v___f_3428_, 6, v___x_3427_);
lean_closure_set(v___f_3428_, 7, v_a_3412_);
v___x_3429_ = 0;
v___x_3430_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3421_, v_binderInfo_3424_, v_a_3426_, v___f_3428_, v___x_3429_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec_ref(v_a_3395_);
return v___x_3430_;
}
else
{
lean_dec_ref(v_body_3423_);
lean_dec(v_binderName_3421_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
return v___x_3425_;
}
}
case 7:
{
lean_object* v_binderName_3431_; lean_object* v_binderType_3432_; lean_object* v_body_3433_; uint8_t v_binderInfo_3434_; lean_object* v___x_3435_; 
v_binderName_3431_ = lean_ctor_get(v_e_3391_, 0);
lean_inc(v_binderName_3431_);
v_binderType_3432_ = lean_ctor_get(v_e_3391_, 1);
lean_inc_ref(v_binderType_3432_);
v_body_3433_ = lean_ctor_get(v_e_3391_, 2);
lean_inc_ref(v_body_3433_);
v_binderInfo_3434_ = lean_ctor_get_uint8(v_e_3391_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3391_, 3);
lean_inc_ref(v_a_3395_);
lean_inc_ref(v_below_3390_);
lean_inc_ref(v_containsRecFn_3389_);
lean_inc_ref(v_recFnNames_3388_);
lean_inc_ref(v_positions_3387_);
lean_inc_ref(v_recArgInfos_3386_);
v___x_3435_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v_below_3390_, v_binderType_3432_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3435_, 1);
v___x_3437_ = lean_box(v___x_3420_);
v___f_3438_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3438_, 0, v_body_3433_);
lean_closure_set(v___f_3438_, 1, v_recArgInfos_3386_);
lean_closure_set(v___f_3438_, 2, v_positions_3387_);
lean_closure_set(v___f_3438_, 3, v_recFnNames_3388_);
lean_closure_set(v___f_3438_, 4, v_containsRecFn_3389_);
lean_closure_set(v___f_3438_, 5, v_below_3390_);
lean_closure_set(v___f_3438_, 6, v___x_3437_);
lean_closure_set(v___f_3438_, 7, v_a_3412_);
v___x_3439_ = 0;
v___x_3440_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3431_, v_binderInfo_3434_, v_a_3436_, v___f_3438_, v___x_3439_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec_ref(v_a_3395_);
return v___x_3440_;
}
else
{
lean_dec_ref(v_body_3433_);
lean_dec(v_binderName_3431_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
return v___x_3435_;
}
}
case 8:
{
lean_object* v_declName_3441_; lean_object* v_type_3442_; lean_object* v_value_3443_; lean_object* v_body_3444_; uint8_t v_nondep_3445_; lean_object* v___x_3446_; 
lean_dec(v_a_3412_);
v_declName_3441_ = lean_ctor_get(v_e_3391_, 0);
lean_inc(v_declName_3441_);
v_type_3442_ = lean_ctor_get(v_e_3391_, 1);
lean_inc_ref(v_type_3442_);
v_value_3443_ = lean_ctor_get(v_e_3391_, 2);
lean_inc_ref(v_value_3443_);
v_body_3444_ = lean_ctor_get(v_e_3391_, 3);
lean_inc_ref(v_body_3444_);
v_nondep_3445_ = lean_ctor_get_uint8(v_e_3391_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3391_, 4);
lean_inc_ref(v_a_3395_);
lean_inc_ref(v_below_3390_);
lean_inc_ref(v_containsRecFn_3389_);
lean_inc_ref(v_recFnNames_3388_);
lean_inc_ref(v_positions_3387_);
lean_inc_ref(v_recArgInfos_3386_);
v___x_3446_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v_below_3390_, v_type_3442_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
lean_inc_ref(v_a_3395_);
lean_inc_ref(v_below_3390_);
lean_inc_ref(v_containsRecFn_3389_);
lean_inc_ref(v_recFnNames_3388_);
lean_inc_ref(v_positions_3387_);
lean_inc_ref(v_recArgInfos_3386_);
v___x_3448_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v_below_3390_, v_value_3443_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; lean_object* v___f_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___f_3450_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3450_, 0, v_body_3444_);
lean_closure_set(v___f_3450_, 1, v_recArgInfos_3386_);
lean_closure_set(v___f_3450_, 2, v_positions_3387_);
lean_closure_set(v___f_3450_, 3, v_recFnNames_3388_);
lean_closure_set(v___f_3450_, 4, v_containsRecFn_3389_);
lean_closure_set(v___f_3450_, 5, v_below_3390_);
v___x_3451_ = 0;
v___x_3452_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3441_, v_a_3447_, v_a_3449_, v___f_3450_, v_nondep_3445_, v___x_3451_, v___x_3420_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec_ref(v_a_3395_);
return v___x_3452_;
}
else
{
lean_dec(v_a_3447_);
lean_dec_ref(v_body_3444_);
lean_dec(v_declName_3441_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
return v___x_3448_;
}
}
else
{
lean_dec_ref(v_body_3444_);
lean_dec_ref(v_value_3443_);
lean_dec(v_declName_3441_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
return v___x_3446_;
}
}
case 10:
{
lean_object* v_data_3453_; lean_object* v_expr_3454_; lean_object* v___x_3455_; 
lean_dec(v_a_3412_);
v_data_3453_ = lean_ctor_get(v_e_3391_, 0);
lean_inc(v_data_3453_);
v_expr_3454_ = lean_ctor_get(v_e_3391_, 1);
lean_inc_ref(v_expr_3454_);
v___x_3455_ = l_Lean_getRecAppSyntax_x3f(v_e_3391_);
lean_dec_ref_known(v_e_3391_, 2);
if (lean_obj_tag(v___x_3455_) == 1)
{
lean_object* v_val_3456_; lean_object* v_toCold_3457_; lean_object* v_options_3458_; lean_object* v_currRecDepth_3459_; lean_object* v_maxRecDepth_3460_; lean_object* v_ref_3461_; lean_object* v_currNamespace_3462_; lean_object* v_openDecls_3463_; lean_object* v_initHeartbeats_3464_; lean_object* v_maxHeartbeats_3465_; lean_object* v_currMacroScope_3466_; uint8_t v_diag_3467_; uint8_t v_suppressElabErrors_3468_; lean_object* v_ref_3469_; lean_object* v___x_3470_; 
lean_dec(v_data_3453_);
v_val_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_val_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v_toCold_3457_ = lean_ctor_get(v_a_3395_, 0);
lean_inc_ref(v_toCold_3457_);
v_options_3458_ = lean_ctor_get(v_a_3395_, 1);
lean_inc_ref(v_options_3458_);
v_currRecDepth_3459_ = lean_ctor_get(v_a_3395_, 2);
lean_inc(v_currRecDepth_3459_);
v_maxRecDepth_3460_ = lean_ctor_get(v_a_3395_, 3);
lean_inc(v_maxRecDepth_3460_);
v_ref_3461_ = lean_ctor_get(v_a_3395_, 4);
lean_inc(v_ref_3461_);
v_currNamespace_3462_ = lean_ctor_get(v_a_3395_, 5);
lean_inc(v_currNamespace_3462_);
v_openDecls_3463_ = lean_ctor_get(v_a_3395_, 6);
lean_inc(v_openDecls_3463_);
v_initHeartbeats_3464_ = lean_ctor_get(v_a_3395_, 7);
lean_inc(v_initHeartbeats_3464_);
v_maxHeartbeats_3465_ = lean_ctor_get(v_a_3395_, 8);
lean_inc(v_maxHeartbeats_3465_);
v_currMacroScope_3466_ = lean_ctor_get(v_a_3395_, 9);
lean_inc(v_currMacroScope_3466_);
v_diag_3467_ = lean_ctor_get_uint8(v_a_3395_, sizeof(void*)*10);
v_suppressElabErrors_3468_ = lean_ctor_get_uint8(v_a_3395_, sizeof(void*)*10 + 1);
lean_dec_ref(v_a_3395_);
v_ref_3469_ = l_Lean_replaceRef(v_val_3456_, v_ref_3461_);
lean_dec(v_ref_3461_);
lean_dec(v_val_3456_);
v___x_3470_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3470_, 0, v_toCold_3457_);
lean_ctor_set(v___x_3470_, 1, v_options_3458_);
lean_ctor_set(v___x_3470_, 2, v_currRecDepth_3459_);
lean_ctor_set(v___x_3470_, 3, v_maxRecDepth_3460_);
lean_ctor_set(v___x_3470_, 4, v_ref_3469_);
lean_ctor_set(v___x_3470_, 5, v_currNamespace_3462_);
lean_ctor_set(v___x_3470_, 6, v_openDecls_3463_);
lean_ctor_set(v___x_3470_, 7, v_initHeartbeats_3464_);
lean_ctor_set(v___x_3470_, 8, v_maxHeartbeats_3465_);
lean_ctor_set(v___x_3470_, 9, v_currMacroScope_3466_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*10, v_diag_3467_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*10 + 1, v_suppressElabErrors_3468_);
v_e_3391_ = v_expr_3454_;
v_a_3395_ = v___x_3470_;
goto _start;
}
else
{
lean_object* v___x_3472_; 
lean_dec(v___x_3455_);
v___x_3472_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v_below_3390_, v_expr_3454_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3481_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3481_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3481_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3477_ = l_Lean_mkMData(v_data_3453_, v_a_3473_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3477_);
v___x_3479_ = v___x_3475_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
else
{
lean_dec(v_data_3453_);
return v___x_3472_;
}
}
}
case 11:
{
lean_object* v_typeName_3482_; lean_object* v_idx_3483_; lean_object* v_struct_3484_; lean_object* v___x_3485_; 
lean_dec(v_a_3412_);
v_typeName_3482_ = lean_ctor_get(v_e_3391_, 0);
lean_inc(v_typeName_3482_);
v_idx_3483_ = lean_ctor_get(v_e_3391_, 1);
lean_inc(v_idx_3483_);
v_struct_3484_ = lean_ctor_get(v_e_3391_, 2);
lean_inc_ref(v_struct_3484_);
lean_dec_ref_known(v_e_3391_, 3);
v___x_3485_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v_below_3390_, v_struct_3484_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3494_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3490_ = l_Lean_mkProj(v_typeName_3482_, v_idx_3483_, v_a_3486_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v___x_3490_);
v___x_3492_ = v___x_3488_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
else
{
lean_dec(v_idx_3483_);
lean_dec(v_typeName_3482_);
return v___x_3485_;
}
}
case 5:
{
uint8_t v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = lean_unbox(v_a_3412_);
lean_inc_ref(v_e_3391_);
v___x_3496_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3391_, v___x_3495_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
if (lean_obj_tag(v_a_3497_) == 0)
{
lean_dec(v_a_3412_);
v_e_3399_ = v_e_3391_;
v___y_3400_ = v_a_3392_;
v___y_3401_ = v_a_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
goto v___jp_3398_;
}
else
{
lean_object* v_val_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; uint8_t v___x_3501_; 
v_val_3498_ = lean_ctor_get(v_a_3497_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_a_3497_, 1);
v___x_3499_ = lean_unsigned_to_nat(0u);
v___x_3500_ = lean_array_get_size(v_recArgInfos_3386_);
v___x_3501_ = lean_nat_dec_lt(v___x_3499_, v___x_3500_);
if (v___x_3501_ == 0)
{
lean_dec(v_val_3498_);
lean_dec(v_a_3412_);
v_e_3399_ = v_e_3391_;
v___y_3400_ = v_a_3392_;
v___y_3401_ = v_a_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
goto v___jp_3398_;
}
else
{
if (v___x_3501_ == 0)
{
lean_dec(v_val_3498_);
lean_dec(v_a_3412_);
v_e_3399_ = v_e_3391_;
v___y_3400_ = v_a_3392_;
v___y_3401_ = v_a_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
goto v___jp_3398_;
}
else
{
size_t v___x_3502_; size_t v___x_3503_; uint8_t v___x_3504_; 
v___x_3502_ = ((size_t)0ULL);
v___x_3503_ = lean_usize_of_nat(v___x_3500_);
v___x_3504_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3391_, v_recArgInfos_3386_, v___x_3502_, v___x_3503_);
if (v___x_3504_ == 0)
{
lean_dec(v_val_3498_);
lean_dec(v_a_3412_);
v_e_3399_ = v_e_3391_;
v___y_3400_ = v_a_3392_;
v___y_3401_ = v_a_3393_;
v___y_3402_ = v_a_3394_;
v___y_3403_ = v_a_3395_;
v___y_3404_ = v_a_3396_;
goto v___jp_3398_;
}
else
{
lean_object* v_toCold_3505_; lean_object* v_inheritedTraceOptions_3506_; lean_object* v___x_3507_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___x_3578_; 
v_toCold_3505_ = lean_ctor_get(v_a_3395_, 0);
v_inheritedTraceOptions_3506_ = lean_ctor_get(v_toCold_3505_, 4);
v___x_3507_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3578_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3507_, v_inheritedTraceOptions_3506_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; uint8_t v___x_3580_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3578_, 1);
v___x_3580_ = lean_unbox(v_a_3579_);
lean_dec(v_a_3579_);
if (v___x_3580_ == 0)
{
v___y_3509_ = v_a_3392_;
v___y_3510_ = v_a_3393_;
v___y_3511_ = v_a_3394_;
v___y_3512_ = v_a_3395_;
v___y_3513_ = v_a_3396_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3581_; 
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc(v_a_3394_);
lean_inc_ref(v_a_3393_);
lean_inc_ref(v_below_3390_);
v___x_3581_ = lean_infer_type(v_below_3390_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v___x_3583_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3390_);
v___x_3584_ = l_Lean_MessageData_ofExpr(v_below_3390_);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = l_Lean_MessageData_ofExpr(v_a_3582_);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3507_, v___x_3589_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_dec_ref_known(v___x_3590_, 1);
v___y_3509_ = v_a_3392_;
v___y_3510_ = v_a_3393_;
v___y_3511_ = v_a_3394_;
v___y_3512_ = v_a_3395_;
v___y_3513_ = v_a_3396_;
goto v___jp_3508_;
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v_val_3498_);
lean_dec_ref_known(v_e_3391_, 2);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
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
else
{
lean_dec(v_val_3498_);
lean_dec_ref_known(v_e_3391_, 2);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
return v___x_3581_;
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v_val_3498_);
lean_dec_ref_known(v_e_3391_, 2);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v_a_3599_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3578_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3578_);
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
v___jp_3508_:
{
lean_object* v___x_3514_; 
lean_inc_ref(v_below_3390_);
v___x_3514_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3498_, v_below_3390_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
if (lean_obj_tag(v_a_3515_) == 1)
{
lean_object* v_val_3516_; lean_object* v_toMatcherInfo_3517_; lean_object* v_matcherName_3518_; lean_object* v_matcherLevels_3519_; lean_object* v_params_3520_; lean_object* v_motive_3521_; lean_object* v_discrs_3522_; lean_object* v_alts_3523_; lean_object* v_remaining_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; lean_object* v___x_3528_; 
lean_dec_ref(v_below_3390_);
v_val_3516_ = lean_ctor_get(v_a_3515_, 0);
lean_inc(v_val_3516_);
lean_dec_ref_known(v_a_3515_, 1);
v_toMatcherInfo_3517_ = lean_ctor_get(v_val_3516_, 0);
lean_inc_ref(v_toMatcherInfo_3517_);
v_matcherName_3518_ = lean_ctor_get(v_val_3516_, 1);
lean_inc(v_matcherName_3518_);
v_matcherLevels_3519_ = lean_ctor_get(v_val_3516_, 2);
lean_inc_ref(v_matcherLevels_3519_);
v_params_3520_ = lean_ctor_get(v_val_3516_, 3);
lean_inc_ref(v_params_3520_);
v_motive_3521_ = lean_ctor_get(v_val_3516_, 4);
lean_inc_ref(v_motive_3521_);
v_discrs_3522_ = lean_ctor_get(v_val_3516_, 5);
lean_inc_ref(v_discrs_3522_);
v_alts_3523_ = lean_ctor_get(v_val_3516_, 6);
lean_inc_ref(v_alts_3523_);
v_remaining_3524_ = lean_ctor_get(v_val_3516_, 7);
lean_inc_ref(v_remaining_3524_);
v___x_3525_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3516_);
v___x_3526_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3527_ = lean_unbox(v_a_3412_);
lean_dec(v_a_3412_);
v___x_3528_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v___x_3527_, v_e_3391_, v_alts_3523_, v___x_3525_, v___x_3499_, v___x_3526_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v___x_3525_);
lean_dec_ref(v_alts_3523_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3538_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3538_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3538_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3533_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3533_, 0, v_toMatcherInfo_3517_);
lean_ctor_set(v___x_3533_, 1, v_matcherName_3518_);
lean_ctor_set(v___x_3533_, 2, v_matcherLevels_3519_);
lean_ctor_set(v___x_3533_, 3, v_params_3520_);
lean_ctor_set(v___x_3533_, 4, v_motive_3521_);
lean_ctor_set(v___x_3533_, 5, v_discrs_3522_);
lean_ctor_set(v___x_3533_, 6, v_a_3529_);
lean_ctor_set(v___x_3533_, 7, v_remaining_3524_);
v___x_3534_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3533_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3534_);
v___x_3536_ = v___x_3531_;
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
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v_remaining_3524_);
lean_dec_ref(v_discrs_3522_);
lean_dec_ref(v_motive_3521_);
lean_dec_ref(v_params_3520_);
lean_dec_ref(v_matcherLevels_3519_);
lean_dec(v_matcherName_3518_);
lean_dec_ref(v_toMatcherInfo_3517_);
v_a_3539_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3528_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3528_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_object* v_toCold_3547_; lean_object* v_inheritedTraceOptions_3548_; lean_object* v___x_3549_; 
lean_dec(v_a_3515_);
lean_dec(v_a_3412_);
v_toCold_3547_ = lean_ctor_get(v___y_3512_, 0);
v_inheritedTraceOptions_3548_ = lean_ctor_get(v_toCold_3547_, 4);
v___x_3549_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3507_, v_inheritedTraceOptions_3548_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; uint8_t v___x_3551_; 
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___x_3551_ = lean_unbox(v_a_3550_);
lean_dec(v_a_3550_);
if (v___x_3551_ == 0)
{
v_e_3399_ = v_e_3391_;
v___y_3400_ = v___y_3509_;
v___y_3401_ = v___y_3510_;
v___y_3402_ = v___y_3511_;
v___y_3403_ = v___y_3512_;
v___y_3404_ = v___y_3513_;
goto v___jp_3398_;
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3553_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3507_, v___x_3552_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_dec_ref_known(v___x_3553_, 1);
v_e_3399_ = v_e_3391_;
v___y_3400_ = v___y_3509_;
v___y_3401_ = v___y_3510_;
v___y_3402_ = v___y_3511_;
v___y_3403_ = v___y_3512_;
v___y_3404_ = v___y_3513_;
goto v___jp_3398_;
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec_ref(v___y_3512_);
lean_dec_ref_known(v_e_3391_, 2);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v_a_3554_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3553_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3553_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v___y_3512_);
lean_dec_ref_known(v_e_3391_, 2);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v_a_3562_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3549_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3549_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
return v___x_3567_;
}
}
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v___y_3512_);
lean_dec_ref_known(v_e_3391_, 2);
lean_dec(v_a_3412_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v_a_3570_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3514_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3514_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
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
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref_known(v_e_3391_, 2);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v_a_3607_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3496_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3496_);
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
default: 
{
lean_object* v___x_3615_; 
lean_dec(v_a_3412_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
lean_inc_ref(v_e_3391_);
v___x_3615_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3388_, v_e_3391_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
lean_dec_ref(v_a_3395_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3623_);
v___x_3617_ = v___x_3615_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_dec(v___x_3615_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v_e_3391_);
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_e_3391_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec_ref(v_e_3391_);
v_a_3624_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3615_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3615_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
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
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_e_3391_);
lean_dec_ref(v_below_3390_);
lean_dec_ref(v_containsRecFn_3389_);
lean_dec_ref(v_recFnNames_3388_);
lean_dec_ref(v_positions_3387_);
lean_dec_ref(v_recArgInfos_3386_);
v_a_3633_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3411_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3411_);
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
v___jp_3398_:
{
lean_object* v_dummy_3405_; lean_object* v_nargs_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_dummy_3405_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3406_ = l_Lean_Expr_getAppNumArgs(v_e_3399_);
lean_inc(v_nargs_3406_);
v___x_3407_ = lean_mk_array(v_nargs_3406_, v_dummy_3405_);
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_nat_sub(v_nargs_3406_, v___x_3408_);
lean_dec(v_nargs_3406_);
lean_inc_ref(v_e_3399_);
v___x_3410_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3386_, v_positions_3387_, v_recFnNames_3388_, v_containsRecFn_3389_, v_below_3390_, v_e_3399_, v_e_3399_, v___x_3407_, v___x_3409_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec_ref(v___y_3403_);
return v___x_3410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3641_, lean_object* v_recArgInfos_3642_, lean_object* v_positions_3643_, lean_object* v_recFnNames_3644_, lean_object* v_containsRecFn_3645_, lean_object* v_below_3646_, lean_object* v_x_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = lean_expr_instantiate1(v_body_3641_, v_x_3647_);
lean_inc_ref(v___y_3651_);
v___x_3655_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3642_, v_positions_3643_, v_recFnNames_3644_, v_containsRecFn_3645_, v_below_3646_, v___x_3654_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3656_, lean_object* v_positions_3657_, lean_object* v_recFnNames_3658_, lean_object* v_containsRecFn_3659_, lean_object* v_below_3660_, lean_object* v_sz_3661_, lean_object* v_i_3662_, lean_object* v_bs_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
size_t v_sz_boxed_3670_; size_t v_i_boxed_3671_; lean_object* v_res_3672_; 
v_sz_boxed_3670_ = lean_unbox_usize(v_sz_3661_);
lean_dec(v_sz_3661_);
v_i_boxed_3671_ = lean_unbox_usize(v_i_3662_);
lean_dec(v_i_3662_);
v_res_3672_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3656_, v_positions_3657_, v_recFnNames_3658_, v_containsRecFn_3659_, v_below_3660_, v_sz_boxed_3670_, v_i_boxed_3671_, v_bs_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3673_, lean_object* v_positions_3674_, lean_object* v_recFnNames_3675_, lean_object* v_containsRecFn_3676_, lean_object* v_a_3677_, lean_object* v_e_3678_, lean_object* v_as_3679_, lean_object* v_bs_3680_, lean_object* v_i_3681_, lean_object* v_cs_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
uint8_t v_a_28862__boxed_3689_; lean_object* v_res_3690_; 
v_a_28862__boxed_3689_ = lean_unbox(v_a_3677_);
v_res_3690_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3673_, v_positions_3674_, v_recFnNames_3675_, v_containsRecFn_3676_, v_a_28862__boxed_3689_, v_e_3678_, v_as_3679_, v_bs_3680_, v_i_3681_, v_cs_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v_bs_3680_);
lean_dec_ref(v_as_3679_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3691_, lean_object* v_positions_3692_, lean_object* v_recFnNames_3693_, lean_object* v_containsRecFn_3694_, lean_object* v_below_3695_, lean_object* v_e_3696_, lean_object* v_x_3697_, lean_object* v_x_3698_, lean_object* v_x_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3691_, v_positions_3692_, v_recFnNames_3693_, v_containsRecFn_3694_, v_below_3695_, v_e_3696_, v_x_3697_, v_x_3698_, v_x_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3707_, lean_object* v_positions_3708_, lean_object* v_recFnNames_3709_, lean_object* v_containsRecFn_3710_, lean_object* v_below_3711_, lean_object* v_e_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3707_, v_positions_3708_, v_recFnNames_3709_, v_containsRecFn_3710_, v_below_3711_, v_e_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_);
lean_dec(v_a_3717_);
lean_dec(v_a_3715_);
lean_dec_ref(v_a_3714_);
lean_dec(v_a_3713_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3720_, lean_object* v_msg_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3721_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3729_, lean_object* v_msg_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3729_, v_msg_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v___y_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3738_, lean_object* v_name_3739_, lean_object* v_type_3740_, lean_object* v_val_3741_, lean_object* v_k_3742_, uint8_t v_nondep_3743_, uint8_t v_kind_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3739_, v_type_3740_, v_val_3741_, v_k_3742_, v_nondep_3743_, v_kind_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3752_, lean_object* v_name_3753_, lean_object* v_type_3754_, lean_object* v_val_3755_, lean_object* v_k_3756_, lean_object* v_nondep_3757_, lean_object* v_kind_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v_nondep_boxed_3765_; uint8_t v_kind_boxed_3766_; lean_object* v_res_3767_; 
v_nondep_boxed_3765_ = lean_unbox(v_nondep_3757_);
v_kind_boxed_3766_ = lean_unbox(v_kind_3758_);
v_res_3767_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3752_, v_name_3753_, v_type_3754_, v_val_3755_, v_k_3756_, v_nondep_boxed_3765_, v_kind_boxed_3766_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3768_, v___y_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3784_, lean_object* v_msg_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; 
v___x_3792_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3784_, v_msg_3785_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3793_, lean_object* v_msg_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3793_, v_msg_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3802_, lean_object* v_constName_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3811_, lean_object* v_constName_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3811_, v_constName_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3820_, lean_object* v_ref_3821_, lean_object* v_constName_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3821_, v_constName_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3830_, lean_object* v_ref_3831_, lean_object* v_constName_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3830_, v_ref_3831_, v_constName_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec(v_ref_3831_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3840_, lean_object* v_ref_3841_, lean_object* v_msg_3842_, lean_object* v_declHint_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3841_, v_msg_3842_, v_declHint_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3851_, lean_object* v_ref_3852_, lean_object* v_msg_3853_, lean_object* v_declHint_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3851_, v_ref_3852_, v_msg_3853_, v_declHint_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v_ref_3852_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3862_, lean_object* v_declHint_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3862_, v_declHint_3863_, v___y_3868_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3871_, lean_object* v_declHint_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3871_, v_declHint_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3880_, lean_object* v_ref_3881_, lean_object* v_msg_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3881_, v_msg_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_ref_3891_, lean_object* v_msg_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3890_, v_ref_3891_, v_msg_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v_ref_3891_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3900_, lean_object* v_e_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v_fst_3910_; lean_object* v_snd_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3908_ = lean_st_ref_take(v___y_3902_);
v___x_3909_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3900_, v_e_3901_, v___x_3908_);
v_fst_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_fst_3910_);
v_snd_3911_ = lean_ctor_get(v___x_3909_, 1);
lean_inc(v_snd_3911_);
lean_dec_ref(v___x_3909_);
v___x_3912_ = lean_st_ref_put(v___y_3902_, v_snd_3911_);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_fst_3910_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3914_, lean_object* v_e_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3914_, v_e_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec(v___y_3916_);
lean_dec_ref(v_recFnNames_3914_);
return v_res_3922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3923_, size_t v_i_3924_, lean_object* v_bs_3925_){
_start:
{
uint8_t v___x_3926_; 
v___x_3926_ = lean_usize_dec_lt(v_i_3924_, v_sz_3923_);
if (v___x_3926_ == 0)
{
return v_bs_3925_;
}
else
{
lean_object* v_v_3927_; lean_object* v_fnName_3928_; lean_object* v___x_3929_; lean_object* v_bs_x27_3930_; size_t v___x_3931_; size_t v___x_3932_; lean_object* v___x_3933_; 
v_v_3927_ = lean_array_uget_borrowed(v_bs_3925_, v_i_3924_);
v_fnName_3928_ = lean_ctor_get(v_v_3927_, 0);
lean_inc(v_fnName_3928_);
v___x_3929_ = lean_unsigned_to_nat(0u);
v_bs_x27_3930_ = lean_array_uset(v_bs_3925_, v_i_3924_, v___x_3929_);
v___x_3931_ = ((size_t)1ULL);
v___x_3932_ = lean_usize_add(v_i_3924_, v___x_3931_);
v___x_3933_ = lean_array_uset(v_bs_x27_3930_, v_i_3924_, v_fnName_3928_);
v_i_3924_ = v___x_3932_;
v_bs_3925_ = v___x_3933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3935_, lean_object* v_i_3936_, lean_object* v_bs_3937_){
_start:
{
size_t v_sz_boxed_3938_; size_t v_i_boxed_3939_; lean_object* v_res_3940_; 
v_sz_boxed_3938_ = lean_unbox_usize(v_sz_3935_);
lean_dec(v_sz_3935_);
v_i_boxed_3939_ = lean_unbox_usize(v_i_3936_);
lean_dec(v_i_3936_);
v_res_3940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3938_, v_i_boxed_3939_, v_bs_3937_);
return v_res_3940_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3941_ = lean_box(0);
v___x_3942_ = lean_unsigned_to_nat(16u);
v___x_3943_ = lean_mk_array(v___x_3942_, v___x_3941_);
return v___x_3943_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3945_ = lean_unsigned_to_nat(0u);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
lean_ctor_set(v___x_3946_, 1, v___x_3944_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3947_, lean_object* v_positions_3948_, lean_object* v_below_3949_, lean_object* v_e_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; size_t v_sz_3958_; size_t v___x_3959_; lean_object* v_recFnNames_3960_; lean_object* v_containsRecFn_3961_; lean_object* v___x_3962_; 
v___x_3956_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3957_ = lean_st_mk_ref(v___x_3956_);
v_sz_3958_ = lean_array_size(v_recArgInfos_3947_);
v___x_3959_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3947_);
v_recFnNames_3960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3958_, v___x_3959_, v_recArgInfos_3947_);
lean_inc_ref(v_recFnNames_3960_);
v_containsRecFn_3961_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3961_, 0, v_recFnNames_3960_);
lean_inc_ref(v_a_3953_);
v___x_3962_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3947_, v_positions_3948_, v_recFnNames_3960_, v_containsRecFn_3961_, v_below_3949_, v_e_3950_, v___x_3957_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3971_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3971_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3967_ = lean_st_ref_get(v___x_3957_);
lean_dec(v___x_3957_);
lean_dec(v___x_3967_);
if (v_isShared_3966_ == 0)
{
v___x_3969_ = v___x_3965_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3963_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
else
{
lean_dec(v___x_3957_);
return v___x_3962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_3972_, lean_object* v_positions_3973_, lean_object* v_below_3974_, lean_object* v_e_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_3972_, v_positions_3973_, v_below_3974_, v_e_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_3982_, lean_object* v_k_3983_, uint8_t v_cleanupAnnotations_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v___f_3990_; uint8_t v___x_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___f_3990_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3990_, 0, v_k_3983_);
v___x_3991_ = 1;
v___x_3992_ = 0;
v___x_3993_ = lean_box(0);
v___x_3994_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3982_, v___x_3991_, v___x_3992_, v___x_3991_, v___x_3992_, v___x_3993_, v___f_3990_, v_cleanupAnnotations_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3994_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3994_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
v_a_4003_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3994_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3994_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4011_, lean_object* v_k_4012_, lean_object* v_cleanupAnnotations_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4019_; lean_object* v_res_4020_; 
v_cleanupAnnotations_boxed_4019_ = lean_unbox(v_cleanupAnnotations_4013_);
v_res_4020_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4011_, v_k_4012_, v_cleanupAnnotations_boxed_4019_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4021_, lean_object* v_e_4022_, lean_object* v_k_4023_, uint8_t v_cleanupAnnotations_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4022_, v_k_4023_, v_cleanupAnnotations_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4031_, lean_object* v_e_4032_, lean_object* v_k_4033_, lean_object* v_cleanupAnnotations_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4040_; lean_object* v_res_4041_; 
v_cleanupAnnotations_boxed_4040_ = lean_unbox(v_cleanupAnnotations_4034_);
v_res_4041_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4031_, v_e_4032_, v_k_4033_, v_cleanupAnnotations_boxed_4040_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4042_, lean_object* v_recArgInfo_4043_, lean_object* v_xs_4044_, lean_object* v___value_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l_Lean_Meta_instantiateForall(v_type_4042_, v_xs_4044_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4053_; lean_object* v_fst_4054_; lean_object* v_snd_4055_; uint8_t v___x_4056_; uint8_t v___x_4057_; uint8_t v___x_4058_; lean_object* v___x_4059_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref_known(v___x_4051_, 1);
v___x_4053_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4043_, v_xs_4044_);
v_fst_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_fst_4054_);
v_snd_4055_ = lean_ctor_get(v___x_4053_, 1);
lean_inc(v_snd_4055_);
lean_dec_ref(v___x_4053_);
v___x_4056_ = 0;
v___x_4057_ = 1;
v___x_4058_ = 1;
v___x_4059_ = l_Lean_Meta_mkForallFVars(v_snd_4055_, v_a_4052_, v___x_4056_, v___x_4057_, v___x_4057_, v___x_4058_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v_snd_4055_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4061_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___x_4059_, 1);
v___x_4061_ = l_Lean_Meta_mkLambdaFVars(v_fst_4054_, v_a_4060_, v___x_4056_, v___x_4057_, v___x_4056_, v___x_4057_, v___x_4058_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
lean_dec(v_fst_4054_);
return v___x_4061_;
}
else
{
lean_dec(v_fst_4054_);
return v___x_4059_;
}
}
else
{
lean_dec_ref(v_xs_4044_);
lean_dec_ref(v_recArgInfo_4043_);
return v___x_4051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4062_, lean_object* v_recArgInfo_4063_, lean_object* v_xs_4064_, lean_object* v___value_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4062_, v_recArgInfo_4063_, v_xs_4064_, v___value_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
lean_dec(v___y_4069_);
lean_dec_ref(v___y_4068_);
lean_dec(v___y_4067_);
lean_dec_ref(v___y_4066_);
lean_dec_ref(v___value_4065_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4072_, lean_object* v_value_4073_, lean_object* v_type_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v___f_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; 
v___f_4080_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4080_, 0, v_type_4074_);
lean_closure_set(v___f_4080_, 1, v_recArgInfo_4072_);
v___x_4081_ = 0;
v___x_4082_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4073_, v___f_4080_, v___x_4081_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4083_, lean_object* v_value_4084_, lean_object* v_type_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4083_, v_value_4084_, v_type_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4092_, lean_object* v_maxFVars_x3f_4093_, lean_object* v_k_4094_, uint8_t v_cleanupAnnotations_4095_, uint8_t v_whnfType_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___f_4102_; lean_object* v___x_4103_; 
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4102_, 0, v_k_4094_);
v___x_4103_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4092_, v_maxFVars_x3f_4093_, v___f_4102_, v_cleanupAnnotations_4095_, v_whnfType_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
v_a_4112_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4103_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4103_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4120_, lean_object* v_maxFVars_x3f_4121_, lean_object* v_k_4122_, lean_object* v_cleanupAnnotations_4123_, lean_object* v_whnfType_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4130_; uint8_t v_whnfType_boxed_4131_; lean_object* v_res_4132_; 
v_cleanupAnnotations_boxed_4130_ = lean_unbox(v_cleanupAnnotations_4123_);
v_whnfType_boxed_4131_ = lean_unbox(v_whnfType_4124_);
v_res_4132_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4120_, v_maxFVars_x3f_4121_, v_k_4122_, v_cleanupAnnotations_boxed_4130_, v_whnfType_boxed_4131_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4133_, lean_object* v_type_4134_, lean_object* v_maxFVars_x3f_4135_, lean_object* v_k_4136_, uint8_t v_cleanupAnnotations_4137_, uint8_t v_whnfType_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4134_, v_maxFVars_x3f_4135_, v_k_4136_, v_cleanupAnnotations_4137_, v_whnfType_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4145_, lean_object* v_type_4146_, lean_object* v_maxFVars_x3f_4147_, lean_object* v_k_4148_, lean_object* v_cleanupAnnotations_4149_, lean_object* v_whnfType_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4156_; uint8_t v_whnfType_boxed_4157_; lean_object* v_res_4158_; 
v_cleanupAnnotations_boxed_4156_ = lean_unbox(v_cleanupAnnotations_4149_);
v_whnfType_boxed_4157_ = lean_unbox(v_whnfType_4150_);
v_res_4158_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4145_, v_type_4146_, v_maxFVars_x3f_4147_, v_k_4148_, v_cleanupAnnotations_boxed_4156_, v_whnfType_boxed_4157_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4159_, lean_object* v_recArgInfos_4160_, lean_object* v_positions_4161_, lean_object* v_value_4162_, lean_object* v_fst_4163_, lean_object* v_snd_4164_, lean_object* v_below_4165_, lean_object* v_x_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = lean_unsigned_to_nat(0u);
v___x_4173_ = lean_array_get_borrowed(v___x_4159_, v_below_4165_, v___x_4172_);
lean_inc(v___x_4173_);
v___x_4174_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4160_, v_positions_4161_, v___x_4173_, v_value_4162_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; uint8_t v___x_4182_; uint8_t v___x_4183_; lean_object* v___x_4184_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_a_4175_);
lean_dec_ref_known(v___x_4174_, 1);
v___x_4176_ = lean_unsigned_to_nat(1u);
v___x_4177_ = lean_mk_empty_array_with_capacity(v___x_4176_);
lean_inc(v___x_4173_);
v___x_4178_ = lean_array_push(v___x_4177_, v___x_4173_);
v___x_4179_ = l_Array_append___redArg(v_fst_4163_, v___x_4178_);
lean_dec_ref(v___x_4178_);
v___x_4180_ = l_Array_append___redArg(v___x_4179_, v_snd_4164_);
v___x_4181_ = 0;
v___x_4182_ = 1;
v___x_4183_ = 1;
v___x_4184_ = l_Lean_Meta_mkLambdaFVars(v___x_4180_, v_a_4175_, v___x_4181_, v___x_4182_, v___x_4181_, v___x_4182_, v___x_4183_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec_ref(v___x_4180_);
return v___x_4184_;
}
else
{
lean_dec_ref(v_fst_4163_);
return v___x_4174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4185_, lean_object* v_recArgInfos_4186_, lean_object* v_positions_4187_, lean_object* v_value_4188_, lean_object* v_fst_4189_, lean_object* v_snd_4190_, lean_object* v_below_4191_, lean_object* v_x_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4185_, v_recArgInfos_4186_, v_positions_4187_, v_value_4188_, v_fst_4189_, v_snd_4190_, v_below_4191_, v_x_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec_ref(v_x_4192_);
lean_dec_ref(v_below_4191_);
lean_dec_ref(v_snd_4190_);
lean_dec_ref(v___x_4185_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4201_, lean_object* v_FType_4202_, lean_object* v___x_4203_, lean_object* v_recArgInfos_4204_, lean_object* v_positions_4205_, lean_object* v_xs_4206_, lean_object* v_value_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v___x_4213_; lean_object* v_fst_4214_; lean_object* v_snd_4215_; lean_object* v___x_4216_; 
v___x_4213_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4201_, v_xs_4206_);
v_fst_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_fst_4214_);
v_snd_4215_ = lean_ctor_get(v___x_4213_, 1);
lean_inc(v_snd_4215_);
lean_dec_ref(v___x_4213_);
v___x_4216_ = l_Lean_Meta_instantiateForall(v_FType_4202_, v_fst_4214_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___f_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; lean_object* v___x_4221_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref_known(v___x_4216_, 1);
v___f_4218_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4218_, 0, v___x_4203_);
lean_closure_set(v___f_4218_, 1, v_recArgInfos_4204_);
lean_closure_set(v___f_4218_, 2, v_positions_4205_);
lean_closure_set(v___f_4218_, 3, v_value_4207_);
lean_closure_set(v___f_4218_, 4, v_fst_4214_);
lean_closure_set(v___f_4218_, 5, v_snd_4215_);
v___x_4219_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4220_ = 0;
v___x_4221_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4217_, v___x_4219_, v___f_4218_, v___x_4220_, v___x_4220_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
return v___x_4221_;
}
else
{
lean_dec(v_snd_4215_);
lean_dec(v_fst_4214_);
lean_dec_ref(v_value_4207_);
lean_dec_ref(v_positions_4205_);
lean_dec_ref(v_recArgInfos_4204_);
lean_dec_ref(v___x_4203_);
return v___x_4216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4222_, lean_object* v_FType_4223_, lean_object* v___x_4224_, lean_object* v_recArgInfos_4225_, lean_object* v_positions_4226_, lean_object* v_xs_4227_, lean_object* v_value_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4222_, v_FType_4223_, v___x_4224_, v_recArgInfos_4225_, v_positions_4226_, v_xs_4227_, v_value_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4235_, lean_object* v_positions_4236_, lean_object* v_recArgInfo_4237_, lean_object* v_value_4238_, lean_object* v_FType_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_){
_start:
{
lean_object* v___x_4245_; lean_object* v___f_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; 
v___x_4245_ = l_Lean_instInhabitedExpr;
v___f_4246_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4246_, 0, v_recArgInfo_4237_);
lean_closure_set(v___f_4246_, 1, v_FType_4239_);
lean_closure_set(v___f_4246_, 2, v___x_4245_);
lean_closure_set(v___f_4246_, 3, v_recArgInfos_4235_);
lean_closure_set(v___f_4246_, 4, v_positions_4236_);
v___x_4247_ = 0;
v___x_4248_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4238_, v___f_4246_, v___x_4247_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4249_, lean_object* v_positions_4250_, lean_object* v_recArgInfo_4251_, lean_object* v_value_4252_, lean_object* v_FType_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_){
_start:
{
lean_object* v_res_4259_; 
v_res_4259_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4249_, v_positions_4250_, v_recArgInfo_4251_, v_value_4252_, v_FType_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_);
lean_dec(v_a_4257_);
lean_dec_ref(v_a_4256_);
lean_dec(v_a_4255_);
lean_dec_ref(v_a_4254_);
return v_res_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4260_, lean_object* v_params_4261_, uint8_t v_isIndPred_4262_, lean_object* v_brecOnUniv_4263_, lean_object* v_levels_4264_, lean_object* v_idx_4265_){
_start:
{
lean_object* v_n_4266_; lean_object* v___y_4268_; 
v_n_4266_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4260_, v_idx_4265_);
if (v_isIndPred_4262_ == 0)
{
lean_object* v___x_4271_; 
v___x_4271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4271_, 0, v_brecOnUniv_4263_);
lean_ctor_set(v___x_4271_, 1, v_levels_4264_);
v___y_4268_ = v___x_4271_;
goto v___jp_4267_;
}
else
{
lean_dec(v_brecOnUniv_4263_);
v___y_4268_ = v_levels_4264_;
goto v___jp_4267_;
}
v___jp_4267_:
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = l_Lean_Expr_const___override(v_n_4266_, v___y_4268_);
v___x_4270_ = l_Lean_mkAppN(v___x_4269_, v_params_4261_);
return v___x_4270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4272_, lean_object* v_params_4273_, lean_object* v_isIndPred_4274_, lean_object* v_brecOnUniv_4275_, lean_object* v_levels_4276_, lean_object* v_idx_4277_){
_start:
{
uint8_t v_isIndPred_boxed_4278_; lean_object* v_res_4279_; 
v_isIndPred_boxed_4278_ = lean_unbox(v_isIndPred_4274_);
v_res_4279_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4272_, v_params_4273_, v_isIndPred_boxed_4278_, v_brecOnUniv_4275_, v_levels_4276_, v_idx_4277_);
lean_dec(v_idx_4277_);
lean_dec_ref(v_params_4273_);
lean_dec_ref(v_toIndGroupInfo_4272_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4280_, lean_object* v_a_4281_, lean_object* v_n_4282_){
_start:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; 
v___x_4283_ = lean_apply_1(v_brecOnCons_4280_, v_n_4282_);
v___x_4284_ = l_Lean_mkAppN(v___x_4283_, v_a_4281_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4285_, lean_object* v_a_4286_, lean_object* v_n_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4285_, v_a_4286_, v_n_4287_);
lean_dec_ref(v_a_4286_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4289_, lean_object* v_type_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_Lean_Meta_getLevel(v_type_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4297_, lean_object* v_type_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4297_, v_type_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec_ref(v_x_4297_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4305_, size_t v_sz_4306_, size_t v_i_4307_, lean_object* v_bs_4308_){
_start:
{
uint8_t v___x_4309_; 
v___x_4309_ = lean_usize_dec_lt(v_i_4307_, v_sz_4306_);
if (v___x_4309_ == 0)
{
return v_bs_4308_;
}
else
{
lean_object* v___x_4310_; lean_object* v_v_4311_; lean_object* v___x_4312_; lean_object* v_bs_x27_4313_; lean_object* v___x_4314_; size_t v___x_4315_; size_t v___x_4316_; lean_object* v___x_4317_; 
v___x_4310_ = l_Lean_instInhabitedExpr;
v_v_4311_ = lean_array_uget(v_bs_4308_, v_i_4307_);
v___x_4312_ = lean_unsigned_to_nat(0u);
v_bs_x27_4313_ = lean_array_uset(v_bs_4308_, v_i_4307_, v___x_4312_);
v___x_4314_ = lean_array_get_borrowed(v___x_4310_, v_xs_4305_, v_v_4311_);
lean_dec(v_v_4311_);
v___x_4315_ = ((size_t)1ULL);
v___x_4316_ = lean_usize_add(v_i_4307_, v___x_4315_);
lean_inc(v___x_4314_);
v___x_4317_ = lean_array_uset(v_bs_x27_4313_, v_i_4307_, v___x_4314_);
v_i_4307_ = v___x_4316_;
v_bs_4308_ = v___x_4317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4319_, lean_object* v_sz_4320_, lean_object* v_i_4321_, lean_object* v_bs_4322_){
_start:
{
size_t v_sz_boxed_4323_; size_t v_i_boxed_4324_; lean_object* v_res_4325_; 
v_sz_boxed_4323_ = lean_unbox_usize(v_sz_4320_);
lean_dec(v_sz_4320_);
v_i_boxed_4324_ = lean_unbox_usize(v_i_4321_);
lean_dec(v_i_4321_);
v_res_4325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4319_, v_sz_boxed_4323_, v_i_boxed_4324_, v_bs_4322_);
lean_dec_ref(v_xs_4319_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4326_, lean_object* v_f_4327_, lean_object* v_as_4328_, lean_object* v_bs_4329_, lean_object* v_i_4330_, lean_object* v_cs_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = lean_array_get_size(v_as_4328_);
v___x_4338_ = lean_nat_dec_lt(v_i_4330_, v___x_4337_);
if (v___x_4338_ == 0)
{
lean_object* v___x_4339_; 
lean_dec(v_i_4330_);
lean_dec_ref(v_f_4327_);
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v_cs_4331_);
return v___x_4339_;
}
else
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = lean_array_get_size(v_bs_4329_);
v___x_4341_ = lean_nat_dec_lt(v_i_4330_, v___x_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; 
lean_dec(v_i_4330_);
lean_dec_ref(v_f_4327_);
v___x_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4342_, 0, v_cs_4331_);
return v___x_4342_;
}
else
{
lean_object* v_a_4343_; lean_object* v_b_4344_; size_t v_sz_4345_; size_t v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v_a_4343_ = lean_array_fget_borrowed(v_as_4328_, v_i_4330_);
v_b_4344_ = lean_array_fget_borrowed(v_bs_4329_, v_i_4330_);
v_sz_4345_ = lean_array_size(v_b_4344_);
v___x_4346_ = ((size_t)0ULL);
lean_inc(v_b_4344_);
v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4326_, v_sz_4345_, v___x_4346_, v_b_4344_);
lean_inc_ref(v_f_4327_);
lean_inc(v___y_4335_);
lean_inc_ref(v___y_4334_);
lean_inc(v___y_4333_);
lean_inc_ref(v___y_4332_);
lean_inc(v_a_4343_);
v___x_4348_ = lean_apply_7(v_f_4327_, v_a_4343_, v___x_4347_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, lean_box(0));
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4348_, 1);
v___x_4350_ = lean_unsigned_to_nat(1u);
v___x_4351_ = lean_nat_add(v_i_4330_, v___x_4350_);
lean_dec(v_i_4330_);
v___x_4352_ = lean_array_push(v_cs_4331_, v_a_4349_);
v_i_4330_ = v___x_4351_;
v_cs_4331_ = v___x_4352_;
goto _start;
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec_ref(v_cs_4331_);
lean_dec(v_i_4330_);
lean_dec_ref(v_f_4327_);
v_a_4354_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4348_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4348_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4362_, lean_object* v_f_4363_, lean_object* v_as_4364_, lean_object* v_bs_4365_, lean_object* v_i_4366_, lean_object* v_cs_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4362_, v_f_4363_, v_as_4364_, v_bs_4365_, v_i_4366_, v_cs_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec_ref(v_bs_4365_);
lean_dec_ref(v_as_4364_);
lean_dec_ref(v_xs_4362_);
return v_res_4373_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Array_instInhabited(lean_box(0));
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_){
_start:
{
lean_object* v___x_4381_; lean_object* v_toApplicative_4382_; lean_object* v_toFunctor_4383_; lean_object* v_toSeq_4384_; lean_object* v_toSeqLeft_4385_; lean_object* v_toSeqRight_4386_; lean_object* v___f_4387_; lean_object* v___f_4388_; lean_object* v___f_4389_; lean_object* v___f_4390_; lean_object* v___x_4391_; lean_object* v___f_4392_; lean_object* v___f_4393_; lean_object* v___f_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v_toApplicative_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4429_; 
v___x_4381_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4382_ = lean_ctor_get(v___x_4381_, 0);
v_toFunctor_4383_ = lean_ctor_get(v_toApplicative_4382_, 0);
v_toSeq_4384_ = lean_ctor_get(v_toApplicative_4382_, 2);
v_toSeqLeft_4385_ = lean_ctor_get(v_toApplicative_4382_, 3);
v_toSeqRight_4386_ = lean_ctor_get(v_toApplicative_4382_, 4);
v___f_4387_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4388_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4383_, 2);
v___f_4389_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4389_, 0, v_toFunctor_4383_);
v___f_4390_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4390_, 0, v_toFunctor_4383_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___f_4389_);
lean_ctor_set(v___x_4391_, 1, v___f_4390_);
lean_inc(v_toSeqRight_4386_);
v___f_4392_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4392_, 0, v_toSeqRight_4386_);
lean_inc(v_toSeqLeft_4385_);
v___f_4393_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4393_, 0, v_toSeqLeft_4385_);
lean_inc(v_toSeq_4384_);
v___f_4394_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4394_, 0, v_toSeq_4384_);
v___x_4395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4391_);
lean_ctor_set(v___x_4395_, 1, v___f_4387_);
lean_ctor_set(v___x_4395_, 2, v___f_4394_);
lean_ctor_set(v___x_4395_, 3, v___f_4393_);
lean_ctor_set(v___x_4395_, 4, v___f_4392_);
v___x_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
lean_ctor_set(v___x_4396_, 1, v___f_4388_);
v___x_4397_ = l_StateRefT_x27_instMonad___redArg(v___x_4396_);
v_toApplicative_4398_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4429_ == 0)
{
lean_object* v_unused_4430_; 
v_unused_4430_ = lean_ctor_get(v___x_4397_, 1);
lean_dec(v_unused_4430_);
v___x_4400_ = v___x_4397_;
v_isShared_4401_ = v_isSharedCheck_4429_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_toApplicative_4398_);
lean_dec(v___x_4397_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4429_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v_toFunctor_4402_; lean_object* v_toSeq_4403_; lean_object* v_toSeqLeft_4404_; lean_object* v_toSeqRight_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4427_; 
v_toFunctor_4402_ = lean_ctor_get(v_toApplicative_4398_, 0);
v_toSeq_4403_ = lean_ctor_get(v_toApplicative_4398_, 2);
v_toSeqLeft_4404_ = lean_ctor_get(v_toApplicative_4398_, 3);
v_toSeqRight_4405_ = lean_ctor_get(v_toApplicative_4398_, 4);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_toApplicative_4398_);
if (v_isSharedCheck_4427_ == 0)
{
lean_object* v_unused_4428_; 
v_unused_4428_ = lean_ctor_get(v_toApplicative_4398_, 1);
lean_dec(v_unused_4428_);
v___x_4407_ = v_toApplicative_4398_;
v_isShared_4408_ = v_isSharedCheck_4427_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_toSeqRight_4405_);
lean_inc(v_toSeqLeft_4404_);
lean_inc(v_toSeq_4403_);
lean_inc(v_toFunctor_4402_);
lean_dec(v_toApplicative_4398_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4427_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___f_4409_; lean_object* v___f_4410_; lean_object* v___f_4411_; lean_object* v___f_4412_; lean_object* v___x_4413_; lean_object* v___f_4414_; lean_object* v___f_4415_; lean_object* v___f_4416_; lean_object* v___x_4418_; 
v___f_4409_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4410_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4402_);
v___f_4411_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4411_, 0, v_toFunctor_4402_);
v___f_4412_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4412_, 0, v_toFunctor_4402_);
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___f_4411_);
lean_ctor_set(v___x_4413_, 1, v___f_4412_);
v___f_4414_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4414_, 0, v_toSeqRight_4405_);
v___f_4415_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4415_, 0, v_toSeqLeft_4404_);
v___f_4416_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4416_, 0, v_toSeq_4403_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 4, v___f_4414_);
lean_ctor_set(v___x_4407_, 3, v___f_4415_);
lean_ctor_set(v___x_4407_, 2, v___f_4416_);
lean_ctor_set(v___x_4407_, 1, v___f_4409_);
lean_ctor_set(v___x_4407_, 0, v___x_4413_);
v___x_4418_ = v___x_4407_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4426_, 1, v___f_4409_);
lean_ctor_set(v_reuseFailAlloc_4426_, 2, v___f_4416_);
lean_ctor_set(v_reuseFailAlloc_4426_, 3, v___f_4415_);
lean_ctor_set(v_reuseFailAlloc_4426_, 4, v___f_4414_);
v___x_4418_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
lean_object* v___x_4420_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set(v___x_4400_, 1, v___f_4410_);
lean_ctor_set(v___x_4400_, 0, v___x_4418_);
v___x_4420_ = v___x_4400_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4418_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v___f_4410_);
v___x_4420_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_855__overap_4423_; lean_object* v___x_4424_; 
v___x_4421_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4422_ = l_instInhabitedOfMonad___redArg(v___x_4420_, v___x_4421_);
v___x_855__overap_4423_ = lean_panic_fn_borrowed(v___x_4422_, v_msg_4375_);
lean_dec(v___x_4422_);
lean_inc(v___y_4379_);
lean_inc_ref(v___y_4378_);
lean_inc(v___y_4377_);
lean_inc_ref(v___y_4376_);
v___x_4424_ = lean_apply_5(v___x_855__overap_4423_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, lean_box(0));
return v___x_4424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4437_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4441_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4442_ = lean_unsigned_to_nat(2u);
v___x_4443_ = lean_unsigned_to_nat(73u);
v___x_4444_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4445_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4446_ = l_mkPanicMessageWithDecl(v___x_4445_, v___x_4444_, v___x_4443_, v___x_4442_, v___x_4441_);
return v___x_4446_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4448_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4449_ = lean_unsigned_to_nat(2u);
v___x_4450_ = lean_unsigned_to_nat(74u);
v___x_4451_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4452_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4453_ = l_mkPanicMessageWithDecl(v___x_4452_, v___x_4451_, v___x_4450_, v___x_4449_, v___x_4448_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4456_, lean_object* v_positions_4457_, lean_object* v_ys_4458_, lean_object* v_xs_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; uint8_t v___x_4467_; 
v___x_4465_ = lean_array_get_size(v_positions_4457_);
v___x_4466_ = lean_array_get_size(v_ys_4458_);
v___x_4467_ = lean_nat_dec_eq(v___x_4465_, v___x_4466_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_dec_ref(v_f_4456_);
v___x_4468_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4469_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4468_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
return v___x_4469_;
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; uint8_t v___x_4472_; 
v___x_4470_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4457_);
v___x_4471_ = lean_array_get_size(v_xs_4459_);
v___x_4472_ = lean_nat_dec_eq(v___x_4470_, v___x_4471_);
lean_dec(v___x_4470_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
lean_dec_ref(v_f_4456_);
v___x_4473_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4474_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4473_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
return v___x_4474_;
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = lean_unsigned_to_nat(0u);
v___x_4476_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4477_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4459_, v_f_4456_, v_ys_4458_, v_positions_4457_, v___x_4475_, v___x_4476_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
return v___x_4477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4478_, lean_object* v_positions_4479_, lean_object* v_ys_4480_, lean_object* v_xs_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4478_, v_positions_4479_, v_ys_4480_, v_xs_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec_ref(v_xs_4481_);
lean_dec_ref(v_ys_4480_);
lean_dec_ref(v_positions_4479_);
return v_res_4487_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; 
v___x_4489_ = lean_unsigned_to_nat(0u);
v___x_4490_ = l_Lean_Level_ofNat(v___x_4489_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4491_, lean_object* v_positions_4492_, lean_object* v_motives_4493_, uint8_t v_isIndPred_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v_indGroupInst_4503_; lean_object* v_brecOnUniv_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; 
v___x_4500_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4501_ = lean_unsigned_to_nat(0u);
v___x_4502_ = lean_array_get_borrowed(v___x_4500_, v_recArgInfos_4491_, v___x_4501_);
v_indGroupInst_4503_ = lean_ctor_get(v___x_4502_, 4);
if (v_isIndPred_4494_ == 0)
{
lean_object* v___f_4546_; lean_object* v___x_4547_; lean_object* v_motive_4548_; lean_object* v___x_4549_; 
v___f_4546_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4547_ = l_Lean_instInhabitedExpr;
v_motive_4548_ = lean_array_get_borrowed(v___x_4547_, v_motives_4493_, v___x_4501_);
lean_inc(v_motive_4548_);
v___x_4549_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4548_, v___f_4546_, v_isIndPred_4494_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v_brecOnUniv_4505_ = v_a_4550_;
v___y_4506_ = v_a_4495_;
v___y_4507_ = v_a_4496_;
v___y_4508_ = v_a_4497_;
v___y_4509_ = v_a_4498_;
goto v___jp_4504_;
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
v_a_4551_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4549_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4549_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
else
{
lean_object* v___x_4559_; 
v___x_4559_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4505_ = v___x_4559_;
v___y_4506_ = v_a_4495_;
v___y_4507_ = v_a_4496_;
v___y_4508_ = v_a_4497_;
v___y_4509_ = v_a_4498_;
goto v___jp_4504_;
}
v___jp_4504_:
{
lean_object* v_toIndGroupInfo_4510_; lean_object* v_levels_4511_; lean_object* v_params_4512_; lean_object* v___x_4513_; lean_object* v_brecOnCons_4514_; lean_object* v_brecOnAux_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; 
v_toIndGroupInfo_4510_ = lean_ctor_get(v_indGroupInst_4503_, 0);
v_levels_4511_ = lean_ctor_get(v_indGroupInst_4503_, 1);
v_params_4512_ = lean_ctor_get(v_indGroupInst_4503_, 2);
v___x_4513_ = lean_box(v_isIndPred_4494_);
lean_inc_n(v_levels_4511_, 2);
lean_inc(v_brecOnUniv_4505_);
lean_inc_ref(v_params_4512_);
lean_inc_ref(v_toIndGroupInfo_4510_);
v_brecOnCons_4514_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4514_, 0, v_toIndGroupInfo_4510_);
lean_closure_set(v_brecOnCons_4514_, 1, v_params_4512_);
lean_closure_set(v_brecOnCons_4514_, 2, v___x_4513_);
lean_closure_set(v_brecOnCons_4514_, 3, v_brecOnUniv_4505_);
lean_closure_set(v_brecOnCons_4514_, 4, v_levels_4511_);
v_brecOnAux_4515_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4510_, v_params_4512_, v_isIndPred_4494_, v_brecOnUniv_4505_, v_levels_4511_, v___x_4501_);
v___x_4516_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4510_);
v___x_4517_ = l_Lean_Meta_inferArgumentTypesN(v___x_4516_, v_brecOnAux_4515_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
v___x_4519_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4520_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4519_, v_positions_4492_, v_a_4518_, v_motives_4493_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v_a_4518_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4529_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4529_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4529_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___f_4525_; lean_object* v___x_4527_; 
v___f_4525_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4525_, 0, v_brecOnCons_4514_);
lean_closure_set(v___f_4525_, 1, v_a_4521_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___f_4525_);
v___x_4527_ = v___x_4523_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v___f_4525_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
return v___x_4527_;
}
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
lean_dec_ref(v_brecOnCons_4514_);
v_a_4530_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4520_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4520_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
lean_dec_ref(v_brecOnCons_4514_);
v_a_4538_ = lean_ctor_get(v___x_4517_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4517_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4517_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4517_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4560_, lean_object* v_positions_4561_, lean_object* v_motives_4562_, lean_object* v_isIndPred_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
uint8_t v_isIndPred_boxed_4569_; lean_object* v_res_4570_; 
v_isIndPred_boxed_4569_ = lean_unbox(v_isIndPred_4563_);
v_res_4570_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4560_, v_positions_4561_, v_motives_4562_, v_isIndPred_boxed_4569_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec_ref(v_motives_4562_);
lean_dec_ref(v_positions_4561_);
lean_dec_ref(v_recArgInfos_4560_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4571_, lean_object* v_msg_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v___x_4578_; 
v___x_4578_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4579_, lean_object* v_msg_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_){
_start:
{
lean_object* v_res_4586_; 
v_res_4586_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4579_, v_msg_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v___y_4582_);
lean_dec_ref(v___y_4581_);
return v_res_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4587_, lean_object* v_00_u03b1_4588_, lean_object* v_f_4589_, lean_object* v_positions_4590_, lean_object* v_ys_4591_, lean_object* v_xs_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4589_, v_positions_4590_, v_ys_4591_, v_xs_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
return v___x_4598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4599_, lean_object* v_00_u03b1_4600_, lean_object* v_f_4601_, lean_object* v_positions_4602_, lean_object* v_ys_4603_, lean_object* v_xs_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v_res_4610_; 
v_res_4610_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4599_, v_00_u03b1_4600_, v_f_4601_, v_positions_4602_, v_ys_4603_, v_xs_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec(v___y_4606_);
lean_dec_ref(v___y_4605_);
lean_dec_ref(v_xs_4604_);
lean_dec_ref(v_ys_4603_);
lean_dec_ref(v_positions_4602_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4611_, lean_object* v_00_u03b3_4612_, lean_object* v_xs_4613_, lean_object* v_f_4614_, lean_object* v_as_4615_, lean_object* v_bs_4616_, lean_object* v_i_4617_, lean_object* v_cs_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v___x_4624_; 
v___x_4624_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4613_, v_f_4614_, v_as_4615_, v_bs_4616_, v_i_4617_, v_cs_4618_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
return v___x_4624_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4625_, lean_object* v_00_u03b3_4626_, lean_object* v_xs_4627_, lean_object* v_f_4628_, lean_object* v_as_4629_, lean_object* v_bs_4630_, lean_object* v_i_4631_, lean_object* v_cs_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v_res_4638_; 
v_res_4638_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4625_, v_00_u03b3_4626_, v_xs_4627_, v_f_4628_, v_as_4629_, v_bs_4630_, v_i_4631_, v_cs_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec(v___y_4634_);
lean_dec_ref(v___y_4633_);
lean_dec_ref(v_bs_4630_);
lean_dec_ref(v_as_4629_);
lean_dec_ref(v_xs_4627_);
return v_res_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4639_, lean_object* v_e_4640_){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = l_Lean_indentD(v_e_4640_);
v___x_4642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4639_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
return v___x_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4643_, lean_object* v_x_4644_, lean_object* v_brecOnType_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v___x_4651_; 
v___x_4651_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4643_, v_brecOnType_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
return v___x_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4652_, lean_object* v_x_4653_, lean_object* v_brecOnType_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_){
_start:
{
lean_object* v_res_4660_; 
v_res_4660_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4652_, v_x_4653_, v_brecOnType_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec_ref(v_x_4653_);
return v_res_4660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4661_, lean_object* v_as_4662_, size_t v_sz_4663_, size_t v_i_4664_, lean_object* v_b_4665_){
_start:
{
uint8_t v___x_4667_; 
v___x_4667_ = lean_usize_dec_lt(v_i_4664_, v_sz_4663_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; 
lean_dec_ref(v_a_4661_);
v___x_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4668_, 0, v_b_4665_);
return v___x_4668_;
}
else
{
lean_object* v_a_4669_; lean_object* v___x_4670_; size_t v___x_4671_; size_t v___x_4672_; 
v_a_4669_ = lean_array_uget_borrowed(v_as_4662_, v_i_4664_);
lean_inc_ref(v_a_4661_);
v___x_4670_ = lean_array_set(v_b_4665_, v_a_4669_, v_a_4661_);
v___x_4671_ = ((size_t)1ULL);
v___x_4672_ = lean_usize_add(v_i_4664_, v___x_4671_);
v_i_4664_ = v___x_4672_;
v_b_4665_ = v___x_4670_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4674_, lean_object* v_as_4675_, lean_object* v_sz_4676_, lean_object* v_i_4677_, lean_object* v_b_4678_, lean_object* v___y_4679_){
_start:
{
size_t v_sz_boxed_4680_; size_t v_i_boxed_4681_; lean_object* v_res_4682_; 
v_sz_boxed_4680_ = lean_unbox_usize(v_sz_4676_);
lean_dec(v_sz_4676_);
v_i_boxed_4681_ = lean_unbox_usize(v_i_4677_);
lean_dec(v_i_4677_);
v_res_4682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4674_, v_as_4675_, v_sz_boxed_4680_, v_i_boxed_4681_, v_b_4678_);
lean_dec_ref(v_as_4675_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4683_, size_t v_sz_4684_, size_t v_i_4685_, lean_object* v_b_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
uint8_t v___x_4692_; 
v___x_4692_ = lean_usize_dec_lt(v_i_4685_, v_sz_4684_);
if (v___x_4692_ == 0)
{
lean_object* v___x_4693_; 
v___x_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4693_, 0, v_b_4686_);
return v___x_4693_;
}
else
{
lean_object* v_snd_4694_; lean_object* v_fst_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4739_; 
v_snd_4694_ = lean_ctor_get(v_b_4686_, 1);
v_fst_4695_ = lean_ctor_get(v_b_4686_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v_b_4686_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4697_ = v_b_4686_;
v_isShared_4698_ = v_isSharedCheck_4739_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_snd_4694_);
lean_inc(v_fst_4695_);
lean_dec(v_b_4686_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4739_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v_array_4699_; lean_object* v_start_4700_; lean_object* v_stop_4701_; uint8_t v___x_4702_; 
v_array_4699_ = lean_ctor_get(v_snd_4694_, 0);
v_start_4700_ = lean_ctor_get(v_snd_4694_, 1);
v_stop_4701_ = lean_ctor_get(v_snd_4694_, 2);
v___x_4702_ = lean_nat_dec_lt(v_start_4700_, v_stop_4701_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4704_; 
if (v_isShared_4698_ == 0)
{
v___x_4704_ = v___x_4697_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_fst_4695_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v_snd_4694_);
v___x_4704_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4705_, 0, v___x_4704_);
return v___x_4705_;
}
}
else
{
lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4735_; 
lean_inc(v_stop_4701_);
lean_inc(v_start_4700_);
lean_inc_ref(v_array_4699_);
v_isSharedCheck_4735_ = !lean_is_exclusive(v_snd_4694_);
if (v_isSharedCheck_4735_ == 0)
{
lean_object* v_unused_4736_; lean_object* v_unused_4737_; lean_object* v_unused_4738_; 
v_unused_4736_ = lean_ctor_get(v_snd_4694_, 2);
lean_dec(v_unused_4736_);
v_unused_4737_ = lean_ctor_get(v_snd_4694_, 1);
lean_dec(v_unused_4737_);
v_unused_4738_ = lean_ctor_get(v_snd_4694_, 0);
lean_dec(v_unused_4738_);
v___x_4708_ = v_snd_4694_;
v_isShared_4709_ = v_isSharedCheck_4735_;
goto v_resetjp_4707_;
}
else
{
lean_dec(v_snd_4694_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4735_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v_a_4710_; lean_object* v___x_4711_; size_t v_sz_4712_; size_t v___x_4713_; lean_object* v___x_4714_; 
v_a_4710_ = lean_array_uget_borrowed(v_as_4683_, v_i_4685_);
v___x_4711_ = lean_array_fget_borrowed(v_array_4699_, v_start_4700_);
v_sz_4712_ = lean_array_size(v___x_4711_);
v___x_4713_ = ((size_t)0ULL);
lean_inc(v_a_4710_);
v___x_4714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4710_, v___x_4711_, v_sz_4712_, v___x_4713_, v_fst_4695_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4719_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_a_4715_);
lean_dec_ref_known(v___x_4714_, 1);
v___x_4716_ = lean_unsigned_to_nat(1u);
v___x_4717_ = lean_nat_add(v_start_4700_, v___x_4716_);
lean_dec(v_start_4700_);
if (v_isShared_4709_ == 0)
{
lean_ctor_set(v___x_4708_, 1, v___x_4717_);
v___x_4719_ = v___x_4708_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_array_4699_);
lean_ctor_set(v_reuseFailAlloc_4726_, 1, v___x_4717_);
lean_ctor_set(v_reuseFailAlloc_4726_, 2, v_stop_4701_);
v___x_4719_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
lean_object* v___x_4721_; 
if (v_isShared_4698_ == 0)
{
lean_ctor_set(v___x_4697_, 1, v___x_4719_);
lean_ctor_set(v___x_4697_, 0, v_a_4715_);
v___x_4721_ = v___x_4697_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4715_);
lean_ctor_set(v_reuseFailAlloc_4725_, 1, v___x_4719_);
v___x_4721_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
size_t v___x_4722_; size_t v___x_4723_; 
v___x_4722_ = ((size_t)1ULL);
v___x_4723_ = lean_usize_add(v_i_4685_, v___x_4722_);
v_i_4685_ = v___x_4723_;
v_b_4686_ = v___x_4721_;
goto _start;
}
}
}
else
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4734_; 
lean_del_object(v___x_4708_);
lean_dec(v_stop_4701_);
lean_dec(v_start_4700_);
lean_dec_ref(v_array_4699_);
lean_del_object(v___x_4697_);
v_a_4727_ = lean_ctor_get(v___x_4714_, 0);
v_isSharedCheck_4734_ = !lean_is_exclusive(v___x_4714_);
if (v_isSharedCheck_4734_ == 0)
{
v___x_4729_ = v___x_4714_;
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4714_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4734_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v___x_4732_; 
if (v_isShared_4730_ == 0)
{
v___x_4732_ = v___x_4729_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4727_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4740_, lean_object* v_sz_4741_, lean_object* v_i_4742_, lean_object* v_b_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
size_t v_sz_boxed_4749_; size_t v_i_boxed_4750_; lean_object* v_res_4751_; 
v_sz_boxed_4749_ = lean_unbox_usize(v_sz_4741_);
lean_dec(v_sz_4741_);
v_i_boxed_4750_ = lean_unbox_usize(v_i_4742_);
lean_dec(v_i_4742_);
v_res_4751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4740_, v_sz_boxed_4749_, v_i_boxed_4750_, v_b_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec_ref(v_as_4740_);
return v_res_4751_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4753_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4754_ = l_Lean_stringToMessageData(v___x_4753_);
return v___x_4754_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4755_; lean_object* v___f_4756_; 
v___x_4755_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4756_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4756_, 0, v___x_4755_);
return v___f_4756_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4757_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4758_ = l_Lean_Expr_sort___override(v___x_4757_);
return v___x_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4759_, lean_object* v_positions_4760_, lean_object* v_brecOnConst_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_){
_start:
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v_recArgInfo_4769_; lean_object* v_indicesPos_4770_; lean_object* v_indIdx_4771_; lean_object* v_brecOn_4772_; lean_object* v___f_4773_; uint8_t v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4767_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4768_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4769_ = lean_array_get_borrowed(v___x_4767_, v_recArgInfos_4759_, v___x_4768_);
v_indicesPos_4770_ = lean_ctor_get(v_recArgInfo_4769_, 3);
v_indIdx_4771_ = lean_ctor_get(v_recArgInfo_4769_, 5);
lean_inc(v_indIdx_4771_);
v_brecOn_4772_ = lean_apply_1(v_brecOnConst_4761_, v_indIdx_4771_);
v___f_4773_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4774_ = 0;
v___x_4775_ = lean_box(v___x_4774_);
lean_inc_ref(v_brecOn_4772_);
v___x_4776_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4776_, 0, v_brecOn_4772_);
lean_closure_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4776_, v___f_4773_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v___x_4778_; 
lean_dec_ref_known(v___x_4777_, 1);
lean_inc(v_a_4765_);
lean_inc_ref(v_a_4764_);
lean_inc(v_a_4763_);
lean_inc_ref(v_a_4762_);
v___x_4778_ = lean_infer_type(v_brecOn_4772_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; lean_object* v_numTypeFormers_4780_; lean_object* v___f_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; lean_object* v___x_4787_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref_known(v___x_4778_, 1);
v_numTypeFormers_4780_ = lean_array_get_size(v_positions_4760_);
v___f_4781_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4781_, 0, v_numTypeFormers_4780_);
v___x_4782_ = lean_array_get_size(v_indicesPos_4770_);
v___x_4783_ = lean_unsigned_to_nat(1u);
v___x_4784_ = lean_nat_add(v___x_4782_, v___x_4783_);
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
v___x_4786_ = 0;
v___x_4787_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4779_, v___x_4785_, v___f_4781_, v___x_4786_, v___x_4786_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; size_t v_sz_4794_; size_t v___x_4795_; lean_object* v___x_4796_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v___x_4787_, 1);
v___x_4789_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4760_);
v___x_4790_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4791_ = lean_mk_array(v___x_4789_, v___x_4790_);
v___x_4792_ = l_Array_toSubarray___redArg(v_positions_4760_, v___x_4768_, v_numTypeFormers_4780_);
v___x_4793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4791_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
v_sz_4794_ = lean_array_size(v_a_4788_);
v___x_4795_ = ((size_t)0ULL);
v___x_4796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4788_, v_sz_4794_, v___x_4795_, v___x_4793_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec(v_a_4788_);
if (lean_obj_tag(v___x_4796_) == 0)
{
lean_object* v_a_4797_; lean_object* v___x_4799_; uint8_t v_isShared_4800_; uint8_t v_isSharedCheck_4805_; 
v_a_4797_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4799_ = v___x_4796_;
v_isShared_4800_ = v_isSharedCheck_4805_;
goto v_resetjp_4798_;
}
else
{
lean_inc(v_a_4797_);
lean_dec(v___x_4796_);
v___x_4799_ = lean_box(0);
v_isShared_4800_ = v_isSharedCheck_4805_;
goto v_resetjp_4798_;
}
v_resetjp_4798_:
{
lean_object* v_fst_4801_; lean_object* v___x_4803_; 
v_fst_4801_ = lean_ctor_get(v_a_4797_, 0);
lean_inc(v_fst_4801_);
lean_dec(v_a_4797_);
if (v_isShared_4800_ == 0)
{
lean_ctor_set(v___x_4799_, 0, v_fst_4801_);
v___x_4803_ = v___x_4799_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_fst_4801_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
v_a_4806_ = lean_ctor_get(v___x_4796_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4796_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4796_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4796_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4811_; 
if (v_isShared_4809_ == 0)
{
v___x_4811_ = v___x_4808_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_a_4806_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4760_);
return v___x_4787_;
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
lean_dec_ref(v_positions_4760_);
v_a_4814_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4778_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4778_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec_ref(v_brecOn_4772_);
lean_dec_ref(v_positions_4760_);
v_a_4822_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4777_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4777_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4830_, lean_object* v_positions_4831_, lean_object* v_brecOnConst_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4830_, v_positions_4831_, v_brecOnConst_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec_ref(v_a_4833_);
lean_dec_ref(v_recArgInfos_4830_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4839_, lean_object* v_as_4840_, size_t v_sz_4841_, size_t v_i_4842_, lean_object* v_b_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4839_, v_as_4840_, v_sz_4841_, v_i_4842_, v_b_4843_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4850_, lean_object* v_as_4851_, lean_object* v_sz_4852_, lean_object* v_i_4853_, lean_object* v_b_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
size_t v_sz_boxed_4860_; size_t v_i_boxed_4861_; lean_object* v_res_4862_; 
v_sz_boxed_4860_ = lean_unbox_usize(v_sz_4852_);
lean_dec(v_sz_4852_);
v_i_boxed_4861_ = lean_unbox_usize(v_i_4853_);
lean_dec(v_i_4853_);
v_res_4862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4850_, v_as_4851_, v_sz_boxed_4860_, v_i_boxed_4861_, v_b_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec_ref(v_as_4851_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4863_, lean_object* v_a_4864_){
_start:
{
if (lean_obj_tag(v_a_4863_) == 0)
{
lean_object* v___x_4865_; 
v___x_4865_ = l_List_reverse___redArg(v_a_4864_);
return v___x_4865_;
}
else
{
lean_object* v_head_4866_; lean_object* v_tail_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4878_; 
v_head_4866_ = lean_ctor_get(v_a_4863_, 0);
v_tail_4867_ = lean_ctor_get(v_a_4863_, 1);
v_isSharedCheck_4878_ = !lean_is_exclusive(v_a_4863_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4869_ = v_a_4863_;
v_isShared_4870_ = v_isSharedCheck_4878_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_tail_4867_);
lean_inc(v_head_4866_);
lean_dec(v_a_4863_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4878_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4875_; 
v___x_4871_ = l_Nat_reprFast(v_head_4866_);
v___x_4872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
v___x_4873_ = l_Lean_MessageData_ofFormat(v___x_4872_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 1, v_a_4864_);
lean_ctor_set(v___x_4869_, 0, v___x_4873_);
v___x_4875_ = v___x_4869_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v___x_4873_);
lean_ctor_set(v_reuseFailAlloc_4877_, 1, v_a_4864_);
v___x_4875_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
v_a_4863_ = v_tail_4867_;
v_a_4864_ = v___x_4875_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4879_, lean_object* v_a_4880_){
_start:
{
if (lean_obj_tag(v_a_4879_) == 0)
{
lean_object* v___x_4881_; 
v___x_4881_ = l_List_reverse___redArg(v_a_4880_);
return v___x_4881_;
}
else
{
lean_object* v_head_4882_; lean_object* v_tail_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4895_; 
v_head_4882_ = lean_ctor_get(v_a_4879_, 0);
v_tail_4883_ = lean_ctor_get(v_a_4879_, 1);
v_isSharedCheck_4895_ = !lean_is_exclusive(v_a_4879_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4885_ = v_a_4879_;
v_isShared_4886_ = v_isSharedCheck_4895_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_tail_4883_);
lean_inc(v_head_4882_);
lean_dec(v_a_4879_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4895_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4892_; 
v___x_4887_ = lean_array_to_list(v_head_4882_);
v___x_4888_ = lean_box(0);
v___x_4889_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4887_, v___x_4888_);
v___x_4890_ = l_Lean_MessageData_ofList(v___x_4889_);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 1, v_a_4880_);
lean_ctor_set(v___x_4885_, 0, v___x_4890_);
v___x_4892_ = v___x_4885_;
goto v_reusejp_4891_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v___x_4890_);
lean_ctor_set(v_reuseFailAlloc_4894_, 1, v_a_4880_);
v___x_4892_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4891_;
}
v_reusejp_4891_:
{
v_a_4879_ = v_tail_4883_;
v_a_4880_ = v___x_4892_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4896_, lean_object* v_v_4897_, lean_object* v_i_4898_){
_start:
{
lean_object* v___x_4899_; uint8_t v___x_4900_; 
v___x_4899_ = lean_array_get_size(v_xs_4896_);
v___x_4900_ = lean_nat_dec_lt(v_i_4898_, v___x_4899_);
if (v___x_4900_ == 0)
{
lean_object* v___x_4901_; 
lean_dec(v_i_4898_);
v___x_4901_ = lean_box(0);
return v___x_4901_;
}
else
{
lean_object* v___x_4902_; uint8_t v___x_4903_; 
v___x_4902_ = lean_array_fget_borrowed(v_xs_4896_, v_i_4898_);
v___x_4903_ = lean_nat_dec_eq(v___x_4902_, v_v_4897_);
if (v___x_4903_ == 0)
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = lean_unsigned_to_nat(1u);
v___x_4905_ = lean_nat_add(v_i_4898_, v___x_4904_);
lean_dec(v_i_4898_);
v_i_4898_ = v___x_4905_;
goto _start;
}
else
{
lean_object* v___x_4907_; 
v___x_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4907_, 0, v_i_4898_);
return v___x_4907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4908_, lean_object* v_v_4909_, lean_object* v_i_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4908_, v_v_4909_, v_i_4910_);
lean_dec(v_v_4909_);
lean_dec_ref(v_xs_4908_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4912_, lean_object* v_v_4913_){
_start:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = lean_unsigned_to_nat(0u);
v___x_4915_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4912_, v_v_4913_, v___x_4914_);
return v___x_4915_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4916_, lean_object* v_v_4917_){
_start:
{
lean_object* v_res_4918_; 
v_res_4918_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4916_, v_v_4917_);
lean_dec(v_v_4917_);
lean_dec_ref(v_xs_4916_);
return v_res_4918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4922_, lean_object* v_as_4923_, size_t v_sz_4924_, size_t v_i_4925_, lean_object* v_b_4926_){
_start:
{
uint8_t v___x_4927_; 
v___x_4927_ = lean_usize_dec_lt(v_i_4925_, v_sz_4924_);
if (v___x_4927_ == 0)
{
lean_inc_ref(v_b_4926_);
return v_b_4926_;
}
else
{
lean_object* v___x_4928_; lean_object* v_a_4929_; lean_object* v___x_4930_; 
v___x_4928_ = lean_box(0);
v_a_4929_ = lean_array_uget_borrowed(v_as_4923_, v_i_4925_);
v___x_4930_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4929_, v_fnIdx_4922_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v___x_4931_; size_t v___x_4932_; size_t v___x_4933_; 
v___x_4931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4932_ = ((size_t)1ULL);
v___x_4933_ = lean_usize_add(v_i_4925_, v___x_4932_);
v_i_4925_ = v___x_4933_;
v_b_4926_ = v___x_4931_;
goto _start;
}
else
{
lean_object* v_val_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4946_; 
v_val_4935_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4937_ = v___x_4930_;
v_isShared_4938_ = v_isSharedCheck_4946_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_val_4935_);
lean_dec(v___x_4930_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4946_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4939_ = lean_array_get_size(v_a_4929_);
v___x_4940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
lean_ctor_set(v___x_4940_, 1, v_val_4935_);
if (v_isShared_4938_ == 0)
{
lean_ctor_set(v___x_4937_, 0, v___x_4940_);
v___x_4942_ = v___x_4937_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; 
v___x_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4942_);
v___x_4944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4943_);
lean_ctor_set(v___x_4944_, 1, v___x_4928_);
return v___x_4944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4947_, lean_object* v_as_4948_, lean_object* v_sz_4949_, lean_object* v_i_4950_, lean_object* v_b_4951_){
_start:
{
size_t v_sz_boxed_4952_; size_t v_i_boxed_4953_; lean_object* v_res_4954_; 
v_sz_boxed_4952_ = lean_unbox_usize(v_sz_4949_);
lean_dec(v_sz_4949_);
v_i_boxed_4953_ = lean_unbox_usize(v_i_4950_);
lean_dec(v_i_4950_);
v_res_4954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4947_, v_as_4948_, v_sz_boxed_4952_, v_i_boxed_4953_, v_b_4951_);
lean_dec_ref(v_b_4951_);
lean_dec_ref(v_as_4948_);
lean_dec(v_fnIdx_4947_);
return v_res_4954_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4956_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4957_ = l_Lean_stringToMessageData(v___x_4956_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4958_, lean_object* v_positions_4959_, lean_object* v_fnIdx_4960_, lean_object* v_brecOnConst_4961_, lean_object* v_packedFArgs_4962_, lean_object* v_funTypes_4963_, lean_object* v_ys_4964_, lean_object* v___value_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
lean_object* v___x_4985_; lean_object* v_fst_4986_; lean_object* v_snd_4987_; lean_object* v___x_4988_; size_t v_sz_4989_; size_t v___x_4990_; lean_object* v___x_4991_; lean_object* v_fst_4992_; 
lean_inc_ref(v_ys_4964_);
lean_inc_ref(v_recArgInfo_4958_);
v___x_4985_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4958_, v_ys_4964_);
v_fst_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_fst_4986_);
v_snd_4987_ = lean_ctor_get(v___x_4985_, 1);
lean_inc(v_snd_4987_);
lean_dec_ref(v___x_4985_);
v___x_4988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_4989_ = lean_array_size(v_positions_4959_);
v___x_4990_ = ((size_t)0ULL);
v___x_4991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4960_, v_positions_4959_, v_sz_4989_, v___x_4990_, v___x_4988_);
v_fst_4992_ = lean_ctor_get(v___x_4991_, 0);
lean_inc(v_fst_4992_);
lean_dec_ref(v___x_4991_);
if (lean_obj_tag(v_fst_4992_) == 0)
{
lean_dec(v_snd_4987_);
lean_dec(v_fst_4986_);
lean_dec_ref(v_ys_4964_);
lean_dec_ref(v_brecOnConst_4961_);
lean_dec_ref(v_recArgInfo_4958_);
goto v___jp_4971_;
}
else
{
lean_object* v_val_4993_; 
v_val_4993_ = lean_ctor_get(v_fst_4992_, 0);
lean_inc(v_val_4993_);
lean_dec_ref_known(v_fst_4992_, 1);
if (lean_obj_tag(v_val_4993_) == 1)
{
lean_object* v_val_4994_; lean_object* v_fst_4995_; lean_object* v_snd_4996_; lean_object* v_indIdx_4997_; lean_object* v_brecOn_4998_; lean_object* v_brecOn_4999_; lean_object* v_brecOn_5000_; lean_object* v___x_5001_; 
lean_dec(v_fnIdx_4960_);
lean_dec_ref(v_positions_4959_);
v_val_4994_ = lean_ctor_get(v_val_4993_, 0);
lean_inc(v_val_4994_);
lean_dec_ref_known(v_val_4993_, 1);
v_fst_4995_ = lean_ctor_get(v_val_4994_, 0);
lean_inc(v_fst_4995_);
v_snd_4996_ = lean_ctor_get(v_val_4994_, 1);
lean_inc(v_snd_4996_);
lean_dec(v_val_4994_);
v_indIdx_4997_ = lean_ctor_get(v_recArgInfo_4958_, 5);
lean_inc(v_indIdx_4997_);
lean_dec_ref(v_recArgInfo_4958_);
v_brecOn_4998_ = lean_apply_1(v_brecOnConst_4961_, v_indIdx_4997_);
v_brecOn_4999_ = l_Lean_mkAppN(v_brecOn_4998_, v_fst_4986_);
lean_dec(v_fst_4986_);
v_brecOn_5000_ = l_Lean_mkAppN(v_brecOn_4999_, v_packedFArgs_4962_);
v___x_5001_ = l_Lean_Meta_PProdN_projM(v_fst_4995_, v_snd_4996_, v_brecOn_5000_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
lean_dec(v_snd_4996_);
lean_dec(v_fst_4995_);
if (lean_obj_tag(v___x_5001_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5003_; uint8_t v___x_5004_; uint8_t v___x_5005_; lean_object* v___x_5006_; 
v_a_5002_ = lean_ctor_get(v___x_5001_, 0);
lean_inc(v_a_5002_);
lean_dec_ref_known(v___x_5001_, 1);
v___x_5003_ = l_Lean_mkAppN(v_a_5002_, v_snd_4987_);
lean_dec(v_snd_4987_);
v___x_5004_ = 1;
v___x_5005_ = 1;
v___x_5006_ = l_Lean_Meta_mkLetFVars(v_funTypes_4963_, v___x_5003_, v___x_5004_, v___x_5004_, v___x_5005_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v_a_5007_; uint8_t v___x_5008_; lean_object* v___x_5009_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5007_);
lean_dec_ref_known(v___x_5006_, 1);
v___x_5008_ = 0;
v___x_5009_ = l_Lean_Meta_mkLambdaFVars(v_ys_4964_, v_a_5007_, v___x_5008_, v___x_5004_, v___x_5008_, v___x_5004_, v___x_5005_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
lean_dec_ref(v_ys_4964_);
return v___x_5009_;
}
else
{
lean_dec_ref(v_ys_4964_);
return v___x_5006_;
}
}
else
{
lean_dec(v_snd_4987_);
lean_dec_ref(v_ys_4964_);
return v___x_5001_;
}
}
else
{
lean_dec(v_val_4993_);
lean_dec(v_snd_4987_);
lean_dec(v_fst_4986_);
lean_dec_ref(v_ys_4964_);
lean_dec_ref(v_brecOnConst_4961_);
lean_dec_ref(v_recArgInfo_4958_);
goto v___jp_4971_;
}
}
v___jp_4971_:
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4972_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_4973_ = l_Nat_reprFast(v_fnIdx_4960_);
v___x_4974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4973_);
v___x_4975_ = l_Lean_MessageData_ofFormat(v___x_4974_);
v___x_4976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4972_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
v___x_4977_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_4978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set(v___x_4978_, 1, v___x_4977_);
v___x_4979_ = lean_array_to_list(v_positions_4959_);
v___x_4980_ = lean_box(0);
v___x_4981_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_4979_, v___x_4980_);
v___x_4982_ = l_Lean_MessageData_ofList(v___x_4981_);
v___x_4983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4978_);
lean_ctor_set(v___x_4983_, 1, v___x_4982_);
v___x_4984_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4983_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_);
return v___x_4984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5010_, lean_object* v_positions_5011_, lean_object* v_fnIdx_5012_, lean_object* v_brecOnConst_5013_, lean_object* v_packedFArgs_5014_, lean_object* v_funTypes_5015_, lean_object* v_ys_5016_, lean_object* v___value_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_){
_start:
{
lean_object* v_res_5023_; 
v_res_5023_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5010_, v_positions_5011_, v_fnIdx_5012_, v_brecOnConst_5013_, v_packedFArgs_5014_, v_funTypes_5015_, v_ys_5016_, v___value_5017_, v___y_5018_, v___y_5019_, v___y_5020_, v___y_5021_);
lean_dec(v___y_5021_);
lean_dec_ref(v___y_5020_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec_ref(v___value_5017_);
lean_dec_ref(v_funTypes_5015_);
lean_dec_ref(v_packedFArgs_5014_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5024_, lean_object* v_fnIdx_5025_, lean_object* v_brecOnConst_5026_, lean_object* v_packedFArgs_5027_, lean_object* v_funTypes_5028_, lean_object* v_recArgInfo_5029_, lean_object* v_value_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v___f_5036_; uint8_t v___x_5037_; lean_object* v___x_5038_; 
v___f_5036_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5036_, 0, v_recArgInfo_5029_);
lean_closure_set(v___f_5036_, 1, v_positions_5024_);
lean_closure_set(v___f_5036_, 2, v_fnIdx_5025_);
lean_closure_set(v___f_5036_, 3, v_brecOnConst_5026_);
lean_closure_set(v___f_5036_, 4, v_packedFArgs_5027_);
lean_closure_set(v___f_5036_, 5, v_funTypes_5028_);
v___x_5037_ = 0;
v___x_5038_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5030_, v___f_5036_, v___x_5037_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5039_, lean_object* v_fnIdx_5040_, lean_object* v_brecOnConst_5041_, lean_object* v_packedFArgs_5042_, lean_object* v_funTypes_5043_, lean_object* v_recArgInfo_5044_, lean_object* v_value_5045_, lean_object* v_a_5046_, lean_object* v_a_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_){
_start:
{
lean_object* v_res_5051_; 
v_res_5051_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5039_, v_fnIdx_5040_, v_brecOnConst_5041_, v_packedFArgs_5042_, v_funTypes_5043_, v_recArgInfo_5044_, v_value_5045_, v_a_5046_, v_a_5047_, v_a_5048_, v_a_5049_);
lean_dec(v_a_5049_);
lean_dec_ref(v_a_5048_);
lean_dec(v_a_5047_);
lean_dec_ref(v_a_5046_);
return v_res_5051_;
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
