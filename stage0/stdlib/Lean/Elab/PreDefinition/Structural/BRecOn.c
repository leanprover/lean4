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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object*);
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
v___x_1072_ = lean_mk_array(v___y_1064_, v___x_1071_);
v___x_1073_ = lean_array_get_size(v___y_1066_);
v___x_1074_ = l_Array_toSubarray___redArg(v___y_1066_, v___y_1065_, v___x_1073_);
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
v___x_8862__overap_1087_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1044_, v___x_1041_, v_a_1085_, v___y_1063_, v___x_1086_);
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
lean_dec_ref(v___y_1063_);
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
lean_dec_ref(v___y_1063_);
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
v___x_1115_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1045_, v___x_1114_, v___y_1106_, v___y_1111_, v___y_1110_, v___y_1107_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
lean_inc_ref(v___f_1046_);
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1106_);
v___x_1117_ = lean_apply_5(v___f_1046_, v___y_1106_, v___y_1111_, v___y_1110_, v___y_1107_, lean_box(0));
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
v___y_1063_ = v___f_1125_;
v___y_1064_ = v___x_1126_;
v___y_1065_ = v___y_1109_;
v___y_1066_ = v_a_1116_;
v___y_1067_ = v___y_1106_;
v___y_1068_ = v___y_1111_;
v___y_1069_ = v___y_1110_;
v___y_1070_ = v___y_1107_;
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
lean_inc(v___y_1107_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1106_);
v___x_1142_ = lean_apply_5(v___x_8901__overap_1141_, v___y_1106_, v___y_1111_, v___y_1110_, v___y_1107_, lean_box(0));
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref_known(v___x_1142_, 1);
v___y_1063_ = v___f_1125_;
v___y_1064_ = v___x_1126_;
v___y_1065_ = v___y_1109_;
v___y_1066_ = v_a_1116_;
v___y_1067_ = v___y_1106_;
v___y_1068_ = v___y_1111_;
v___y_1069_ = v___y_1110_;
v___y_1070_ = v___y_1107_;
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
v___y_1106_ = v___y_1170_;
v___y_1107_ = v___y_1173_;
v___y_1108_ = v___x_1175_;
v___y_1109_ = v___x_1174_;
v___y_1110_ = v___y_1172_;
v___y_1111_ = v___y_1171_;
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
v___y_1106_ = v___y_1170_;
v___y_1107_ = v___y_1173_;
v___y_1108_ = v___x_1175_;
v___y_1109_ = v___x_1174_;
v___y_1110_ = v___y_1172_;
v___y_1111_ = v___y_1171_;
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
v___x_1695_ = lean_st_ref_set(v___y_1639_, v___x_1694_);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1716_, lean_object* v_opt_1717_){
_start:
{
lean_object* v_name_1718_; lean_object* v_defValue_1719_; lean_object* v_map_1720_; lean_object* v___x_1721_; 
v_name_1718_ = lean_ctor_get(v_opt_1717_, 0);
v_defValue_1719_ = lean_ctor_get(v_opt_1717_, 1);
v_map_1720_ = lean_ctor_get(v_opts_1716_, 0);
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1720_, v_name_1718_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_inc(v_defValue_1719_);
return v_defValue_1719_;
}
else
{
lean_object* v_val_1722_; 
v_val_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v___x_1721_, 1);
if (lean_obj_tag(v_val_1722_) == 3)
{
lean_object* v_v_1723_; 
v_v_1723_ = lean_ctor_get(v_val_1722_, 0);
lean_inc(v_v_1723_);
lean_dec_ref_known(v_val_1722_, 1);
return v_v_1723_;
}
else
{
lean_dec(v_val_1722_);
lean_inc(v_defValue_1719_);
return v_defValue_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1724_, lean_object* v_opt_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1724_, v_opt_1725_);
lean_dec_ref(v_opt_1725_);
lean_dec_ref(v_opts_1724_);
return v_res_1726_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1727_){
_start:
{
if (lean_obj_tag(v_e_1727_) == 0)
{
uint8_t v___x_1728_; 
v___x_1728_ = 2;
return v___x_1728_;
}
else
{
lean_object* v_a_1729_; uint8_t v___x_1730_; 
v_a_1729_ = lean_ctor_get(v_e_1727_, 0);
v___x_1730_ = l_Lean_Expr_hasSyntheticSorry(v_a_1729_);
if (v___x_1730_ == 0)
{
uint8_t v___x_1731_; 
v___x_1731_ = 0;
return v___x_1731_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = 1;
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1733_){
_start:
{
uint8_t v_res_1734_; lean_object* v_r_1735_; 
v_res_1734_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1733_);
lean_dec_ref(v_e_1733_);
v_r_1735_ = lean_box(v_res_1734_);
return v_r_1735_;
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
v_result_1798_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1775_);
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
v___x_1836_ = lean_st_ref_set(v___y_1773_, v___x_1835_);
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
v___x_1905_ = lean_float_of_nat(v___y_1902_);
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
v___x_1914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1896_, v_hasTrace_1891_, v___x_1897_, v_options_1889_, v___x_1899_, v___y_1901_, v___f_1895_, v___x_1913_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
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
v___y_1901_ = v_a_1929_;
v___y_1902_ = v___x_1932_;
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
v___y_1901_ = v_a_1929_;
v___y_1902_ = v___x_1932_;
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2159_, lean_object* v_msg_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_ref_2166_; lean_object* v___x_2167_; lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2212_; 
v_ref_2166_ = lean_ctor_get(v___y_2163_, 5);
v___x_2167_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2212_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2212_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v_traceState_2173_; lean_object* v_env_2174_; lean_object* v_nextMacroScope_2175_; lean_object* v_ngen_2176_; lean_object* v_auxDeclNGen_2177_; lean_object* v_cache_2178_; lean_object* v_messages_2179_; lean_object* v_infoState_2180_; lean_object* v_snapshotTasks_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2211_; 
v___x_2172_ = lean_st_ref_take(v___y_2164_);
v_traceState_2173_ = lean_ctor_get(v___x_2172_, 4);
v_env_2174_ = lean_ctor_get(v___x_2172_, 0);
v_nextMacroScope_2175_ = lean_ctor_get(v___x_2172_, 1);
v_ngen_2176_ = lean_ctor_get(v___x_2172_, 2);
v_auxDeclNGen_2177_ = lean_ctor_get(v___x_2172_, 3);
v_cache_2178_ = lean_ctor_get(v___x_2172_, 5);
v_messages_2179_ = lean_ctor_get(v___x_2172_, 6);
v_infoState_2180_ = lean_ctor_get(v___x_2172_, 7);
v_snapshotTasks_2181_ = lean_ctor_get(v___x_2172_, 8);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2183_ = v___x_2172_;
v_isShared_2184_ = v_isSharedCheck_2211_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_snapshotTasks_2181_);
lean_inc(v_infoState_2180_);
lean_inc(v_messages_2179_);
lean_inc(v_cache_2178_);
lean_inc(v_traceState_2173_);
lean_inc(v_auxDeclNGen_2177_);
lean_inc(v_ngen_2176_);
lean_inc(v_nextMacroScope_2175_);
lean_inc(v_env_2174_);
lean_dec(v___x_2172_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2211_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
uint64_t v_tid_2185_; lean_object* v_traces_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2210_; 
v_tid_2185_ = lean_ctor_get_uint64(v_traceState_2173_, sizeof(void*)*1);
v_traces_2186_ = lean_ctor_get(v_traceState_2173_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_traceState_2173_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2188_ = v_traceState_2173_;
v_isShared_2189_ = v_isSharedCheck_2210_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_traces_2186_);
lean_dec(v_traceState_2173_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2210_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; double v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2190_ = lean_box(0);
v___x_2191_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2192_ = 0;
v___x_2193_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2194_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2194_, 0, v_cls_2159_);
lean_ctor_set(v___x_2194_, 1, v___x_2190_);
lean_ctor_set(v___x_2194_, 2, v___x_2193_);
lean_ctor_set_float(v___x_2194_, sizeof(void*)*3, v___x_2191_);
lean_ctor_set_float(v___x_2194_, sizeof(void*)*3 + 8, v___x_2191_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*3 + 16, v___x_2192_);
v___x_2195_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2196_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v_a_2168_);
lean_ctor_set(v___x_2196_, 2, v___x_2195_);
lean_inc(v_ref_2166_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_ref_2166_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_PersistentArray_push___redArg(v_traces_2186_, v___x_2197_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 0, v___x_2198_);
v___x_2200_ = v___x_2188_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2198_);
lean_ctor_set_uint64(v_reuseFailAlloc_2209_, sizeof(void*)*1, v_tid_2185_);
v___x_2200_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2202_; 
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 4, v___x_2200_);
v___x_2202_ = v___x_2183_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_env_2174_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_nextMacroScope_2175_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_ngen_2176_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_auxDeclNGen_2177_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2208_, 5, v_cache_2178_);
lean_ctor_set(v_reuseFailAlloc_2208_, 6, v_messages_2179_);
lean_ctor_set(v_reuseFailAlloc_2208_, 7, v_infoState_2180_);
lean_ctor_set(v_reuseFailAlloc_2208_, 8, v_snapshotTasks_2181_);
v___x_2202_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2203_ = lean_st_ref_set(v___y_2164_, v___x_2202_);
v___x_2204_ = lean_box(0);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2204_);
v___x_2206_ = v___x_2170_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2213_, lean_object* v_msg_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2213_, v_msg_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2220_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2221_, lean_object* v_as_2222_, size_t v_i_2223_, size_t v_stop_2224_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_usize_dec_eq(v_i_2223_, v_stop_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; lean_object* v_fnName_2227_; lean_object* v_recArgPos_2228_; uint8_t v___x_2229_; 
v___x_2226_ = lean_array_uget_borrowed(v_as_2222_, v_i_2223_);
v_fnName_2227_ = lean_ctor_get(v___x_2226_, 0);
v_recArgPos_2228_ = lean_ctor_get(v___x_2226_, 2);
lean_inc(v_recArgPos_2228_);
lean_inc(v_fnName_2227_);
v___x_2229_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2227_, v_recArgPos_2228_, v_e_2221_);
if (v___x_2229_ == 0)
{
size_t v___x_2230_; size_t v___x_2231_; 
v___x_2230_ = ((size_t)1ULL);
v___x_2231_ = lean_usize_add(v_i_2223_, v___x_2230_);
v_i_2223_ = v___x_2231_;
goto _start;
}
else
{
return v___x_2229_;
}
}
else
{
uint8_t v___x_2233_; 
v___x_2233_ = 0;
return v___x_2233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2234_, lean_object* v_as_2235_, lean_object* v_i_2236_, lean_object* v_stop_2237_){
_start:
{
size_t v_i_boxed_2238_; size_t v_stop_boxed_2239_; uint8_t v_res_2240_; lean_object* v_r_2241_; 
v_i_boxed_2238_ = lean_unbox_usize(v_i_2236_);
lean_dec(v_i_2236_);
v_stop_boxed_2239_ = lean_unbox_usize(v_stop_2237_);
lean_dec(v_stop_2237_);
v_res_2240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2234_, v_as_2235_, v_i_boxed_2238_, v_stop_boxed_2239_);
lean_dec_ref(v_as_2235_);
lean_dec_ref(v_e_2234_);
v_r_2241_ = lean_box(v_res_2240_);
return v_r_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2242_, lean_object* v_____do__lift_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_options_2250_; uint8_t v_hasTrace_2251_; 
v_options_2250_ = lean_ctor_get(v___y_2247_, 2);
v_hasTrace_2251_ = lean_ctor_get_uint8(v_options_2250_, sizeof(void*)*1);
if (v_hasTrace_2251_ == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_dec(v___x_2242_);
v___x_2252_ = lean_box(v_hasTrace_2251_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2252_);
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2255_ = l_Lean_Name_append(v___x_2254_, v___x_2242_);
v___x_2256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2243_, v_options_2250_, v___x_2255_);
lean_dec(v___x_2255_);
v___x_2257_ = lean_box(v___x_2256_);
v___x_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
return v___x_2258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2259_, lean_object* v_____do__lift_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2259_, v_____do__lift_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v_____do__lift_2260_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; lean_object* v_env_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2271_ = lean_st_ref_get(v___y_2269_);
v_env_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc_ref(v_env_2272_);
lean_dec(v___x_2271_);
v___x_2273_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2272_, v_declName_2268_);
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2275_, v___y_2276_);
lean_dec(v___y_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; lean_object* v_toApplicative_2287_; lean_object* v_toFunctor_2288_; lean_object* v_toSeq_2289_; lean_object* v_toSeqLeft_2290_; lean_object* v_toSeqRight_2291_; lean_object* v___f_2292_; lean_object* v___f_2293_; lean_object* v___f_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___f_2298_; lean_object* v___f_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v_toApplicative_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2335_; 
v___x_2286_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2287_ = lean_ctor_get(v___x_2286_, 0);
v_toFunctor_2288_ = lean_ctor_get(v_toApplicative_2287_, 0);
v_toSeq_2289_ = lean_ctor_get(v_toApplicative_2287_, 2);
v_toSeqLeft_2290_ = lean_ctor_get(v_toApplicative_2287_, 3);
v_toSeqRight_2291_ = lean_ctor_get(v_toApplicative_2287_, 4);
v___f_2292_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2288_, 2);
v___f_2294_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2294_, 0, v_toFunctor_2288_);
v___f_2295_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2295_, 0, v_toFunctor_2288_);
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___f_2294_);
lean_ctor_set(v___x_2296_, 1, v___f_2295_);
lean_inc(v_toSeqRight_2291_);
v___f_2297_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2297_, 0, v_toSeqRight_2291_);
lean_inc(v_toSeqLeft_2290_);
v___f_2298_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2298_, 0, v_toSeqLeft_2290_);
lean_inc(v_toSeq_2289_);
v___f_2299_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2299_, 0, v_toSeq_2289_);
v___x_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2296_);
lean_ctor_set(v___x_2300_, 1, v___f_2292_);
lean_ctor_set(v___x_2300_, 2, v___f_2299_);
lean_ctor_set(v___x_2300_, 3, v___f_2298_);
lean_ctor_set(v___x_2300_, 4, v___f_2297_);
v___x_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
lean_ctor_set(v___x_2301_, 1, v___f_2293_);
v___x_2302_ = l_StateRefT_x27_instMonad___redArg(v___x_2301_);
v_toApplicative_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v___x_2302_, 1);
lean_dec(v_unused_2336_);
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2335_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_toApplicative_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2335_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_toFunctor_2307_; lean_object* v_toSeq_2308_; lean_object* v_toSeqLeft_2309_; lean_object* v_toSeqRight_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2333_; 
v_toFunctor_2307_ = lean_ctor_get(v_toApplicative_2303_, 0);
v_toSeq_2308_ = lean_ctor_get(v_toApplicative_2303_, 2);
v_toSeqLeft_2309_ = lean_ctor_get(v_toApplicative_2303_, 3);
v_toSeqRight_2310_ = lean_ctor_get(v_toApplicative_2303_, 4);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_toApplicative_2303_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; 
v_unused_2334_ = lean_ctor_get(v_toApplicative_2303_, 1);
lean_dec(v_unused_2334_);
v___x_2312_ = v_toApplicative_2303_;
v_isShared_2313_ = v_isSharedCheck_2333_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_toSeqRight_2310_);
lean_inc(v_toSeqLeft_2309_);
lean_inc(v_toSeq_2308_);
lean_inc(v_toFunctor_2307_);
lean_dec(v_toApplicative_2303_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2333_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___f_2314_; lean_object* v___f_2315_; lean_object* v___f_2316_; lean_object* v___f_2317_; lean_object* v___x_2318_; lean_object* v___f_2319_; lean_object* v___f_2320_; lean_object* v___f_2321_; lean_object* v___x_2323_; 
v___f_2314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2315_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2307_);
v___f_2316_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2316_, 0, v_toFunctor_2307_);
v___f_2317_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2317_, 0, v_toFunctor_2307_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___f_2316_);
lean_ctor_set(v___x_2318_, 1, v___f_2317_);
v___f_2319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2319_, 0, v_toSeqRight_2310_);
v___f_2320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2320_, 0, v_toSeqLeft_2309_);
v___f_2321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2321_, 0, v_toSeq_2308_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 4, v___f_2319_);
lean_ctor_set(v___x_2312_, 3, v___f_2320_);
lean_ctor_set(v___x_2312_, 2, v___f_2321_);
lean_ctor_set(v___x_2312_, 1, v___f_2314_);
lean_ctor_set(v___x_2312_, 0, v___x_2318_);
v___x_2323_ = v___x_2312_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___f_2314_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v___f_2321_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v___f_2320_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v___f_2319_);
v___x_2323_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___f_2315_);
lean_ctor_set(v___x_2305_, 0, v___x_2323_);
v___x_2325_ = v___x_2305_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2323_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___f_2315_);
v___x_2325_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_27612__overap_2329_; lean_object* v___x_2330_; 
v___x_2326_ = l_StateRefT_x27_instMonad___redArg(v___x_2325_);
v___x_2327_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2328_ = l_instInhabitedOfMonad___redArg(v___x_2326_, v___x_2327_);
v___x_27612__overap_2329_ = lean_panic_fn_borrowed(v___x_2328_, v_msg_2279_);
lean_dec(v___x_2328_);
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
lean_inc(v___y_2280_);
v___x_2330_ = lean_apply_6(v___x_27612__overap_2329_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, lean_box(0));
return v___x_2330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
return v_res_2344_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2345_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
lean_ctor_set(v___x_2350_, 2, v___x_2349_);
lean_ctor_set(v___x_2350_, 3, v___x_2349_);
lean_ctor_set(v___x_2350_, 4, v___x_2348_);
lean_ctor_set(v___x_2350_, 5, v___x_2348_);
lean_ctor_set(v___x_2350_, 6, v___x_2348_);
lean_ctor_set(v___x_2350_, 7, v___x_2348_);
lean_ctor_set(v___x_2350_, 8, v___x_2348_);
lean_ctor_set(v___x_2350_, 9, v___x_2348_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = lean_unsigned_to_nat(32u);
v___x_2352_ = lean_mk_empty_array_with_capacity(v___x_2351_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2354_ = ((size_t)5ULL);
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = lean_unsigned_to_nat(32u);
v___x_2357_ = lean_mk_empty_array_with_capacity(v___x_2356_);
v___x_2358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2359_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v___x_2357_);
lean_ctor_set(v___x_2359_, 2, v___x_2355_);
lean_ctor_set(v___x_2359_, 3, v___x_2355_);
lean_ctor_set_usize(v___x_2359_, 4, v___x_2354_);
return v___x_2359_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2360_ = lean_box(1);
v___x_2361_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2362_);
lean_ctor_set(v___x_2363_, 1, v___x_2361_);
lean_ctor_set(v___x_2363_, 2, v___x_2360_);
return v___x_2363_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2366_ = l_Lean_stringToMessageData(v___x_2365_);
return v___x_2366_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2372_ = l_Lean_stringToMessageData(v___x_2371_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2375_ = l_Lean_stringToMessageData(v___x_2374_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2384_ = l_Lean_stringToMessageData(v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2385_, lean_object* v_declHint_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v_env_2390_; uint8_t v___x_2391_; 
v___x_2389_ = lean_st_ref_get(v___y_2387_);
v_env_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc_ref(v_env_2390_);
lean_dec(v___x_2389_);
v___x_2391_ = l_Lean_Name_isAnonymous(v_declHint_2386_);
if (v___x_2391_ == 0)
{
uint8_t v_isExporting_2392_; 
v_isExporting_2392_ = lean_ctor_get_uint8(v_env_2390_, sizeof(void*)*8);
if (v_isExporting_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec_ref(v_env_2390_);
lean_dec(v_declHint_2386_);
v___x_2393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2393_, 0, v_msg_2385_);
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; uint8_t v___x_2395_; 
lean_inc_ref(v_env_2390_);
v___x_2394_ = l_Lean_Environment_setExporting(v_env_2390_, v___x_2391_);
lean_inc(v_declHint_2386_);
lean_inc_ref(v___x_2394_);
v___x_2395_ = l_Lean_Environment_contains(v___x_2394_, v_declHint_2386_, v_isExporting_2392_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; 
lean_dec_ref(v___x_2394_);
lean_dec_ref(v_env_2390_);
lean_dec(v_declHint_2386_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v_msg_2385_);
return v___x_2396_;
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v_c_2402_; lean_object* v___x_2403_; 
v___x_2397_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2398_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2399_ = l_Lean_Options_empty;
v___x_2400_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2394_);
lean_ctor_set(v___x_2400_, 1, v___x_2397_);
lean_ctor_set(v___x_2400_, 2, v___x_2398_);
lean_ctor_set(v___x_2400_, 3, v___x_2399_);
lean_inc(v_declHint_2386_);
v___x_2401_ = l_Lean_MessageData_ofConstName(v_declHint_2386_, v___x_2391_);
v_c_2402_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2402_, 0, v___x_2400_);
lean_ctor_set(v_c_2402_, 1, v___x_2401_);
v___x_2403_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2390_, v_declHint_2386_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
lean_dec_ref(v_env_2390_);
lean_dec(v_declHint_2386_);
v___x_2404_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v_c_2402_);
v___x_2406_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = l_Lean_MessageData_note(v___x_2407_);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v_msg_2385_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
else
{
lean_object* v_val_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2446_; 
v_val_2411_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2413_ = v___x_2403_;
v_isShared_2414_ = v_isSharedCheck_2446_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_val_2411_);
lean_dec(v___x_2403_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2446_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_mod_2418_; uint8_t v___x_2419_; 
v___x_2415_ = lean_box(0);
v___x_2416_ = l_Lean_Environment_header(v_env_2390_);
lean_dec_ref(v_env_2390_);
v___x_2417_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2416_);
v_mod_2418_ = lean_array_get(v___x_2415_, v___x_2417_, v_val_2411_);
lean_dec(v_val_2411_);
lean_dec_ref(v___x_2417_);
v___x_2419_ = l_Lean_isPrivateName(v_declHint_2386_);
lean_dec(v_declHint_2386_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2420_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v_c_2402_);
v___x_2422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_MessageData_ofName(v_mod_2418_);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
v___x_2426_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = l_Lean_MessageData_note(v___x_2427_);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v_msg_2385_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2429_);
v___x_2431_ = v___x_2413_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
else
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
v___x_2433_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v_c_2402_);
v___x_2435_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = l_Lean_MessageData_ofName(v_mod_2418_);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
v___x_2441_ = l_Lean_MessageData_note(v___x_2440_);
v___x_2442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2442_, 0, v_msg_2385_);
lean_ctor_set(v___x_2442_, 1, v___x_2441_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2442_);
v___x_2444_ = v___x_2413_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2447_; 
lean_dec_ref(v_env_2390_);
lean_dec(v_declHint_2386_);
v___x_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2447_, 0, v_msg_2385_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2448_, lean_object* v_declHint_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2448_, v_declHint_2449_, v___y_2450_);
lean_dec(v___y_2450_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2453_, lean_object* v_declHint_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2471_; 
v___x_2461_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2453_, v_declHint_2454_, v___y_2459_);
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2471_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2471_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2466_ = l_Lean_unknownIdentifierMessageTag;
v___x_2467_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v_a_2462_);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2467_);
v___x_2469_ = v___x_2464_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2472_, lean_object* v_declHint_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2472_, v_declHint_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_ref_2487_; lean_object* v___x_2488_; lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2497_; 
v_ref_2487_ = lean_ctor_get(v___y_2484_, 5);
v___x_2488_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2491_ = v___x_2488_;
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2488_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2497_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
lean_inc(v_ref_2487_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v_ref_2487_);
lean_ctor_set(v___x_2493_, 1, v_a_2489_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set_tag(v___x_2491_, 1);
lean_ctor_set(v___x_2491_, 0, v___x_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2505_, lean_object* v_msg_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_fileName_2513_; lean_object* v_fileMap_2514_; lean_object* v_options_2515_; lean_object* v_currRecDepth_2516_; lean_object* v_maxRecDepth_2517_; lean_object* v_ref_2518_; lean_object* v_currNamespace_2519_; lean_object* v_openDecls_2520_; lean_object* v_initHeartbeats_2521_; lean_object* v_maxHeartbeats_2522_; lean_object* v_quotContext_2523_; lean_object* v_currMacroScope_2524_; uint8_t v_diag_2525_; lean_object* v_cancelTk_x3f_2526_; uint8_t v_suppressElabErrors_2527_; lean_object* v_inheritedTraceOptions_2528_; lean_object* v_ref_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v_fileName_2513_ = lean_ctor_get(v___y_2510_, 0);
v_fileMap_2514_ = lean_ctor_get(v___y_2510_, 1);
v_options_2515_ = lean_ctor_get(v___y_2510_, 2);
v_currRecDepth_2516_ = lean_ctor_get(v___y_2510_, 3);
v_maxRecDepth_2517_ = lean_ctor_get(v___y_2510_, 4);
v_ref_2518_ = lean_ctor_get(v___y_2510_, 5);
v_currNamespace_2519_ = lean_ctor_get(v___y_2510_, 6);
v_openDecls_2520_ = lean_ctor_get(v___y_2510_, 7);
v_initHeartbeats_2521_ = lean_ctor_get(v___y_2510_, 8);
v_maxHeartbeats_2522_ = lean_ctor_get(v___y_2510_, 9);
v_quotContext_2523_ = lean_ctor_get(v___y_2510_, 10);
v_currMacroScope_2524_ = lean_ctor_get(v___y_2510_, 11);
v_diag_2525_ = lean_ctor_get_uint8(v___y_2510_, sizeof(void*)*14);
v_cancelTk_x3f_2526_ = lean_ctor_get(v___y_2510_, 12);
v_suppressElabErrors_2527_ = lean_ctor_get_uint8(v___y_2510_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2528_ = lean_ctor_get(v___y_2510_, 13);
v_ref_2529_ = l_Lean_replaceRef(v_ref_2505_, v_ref_2518_);
lean_inc_ref(v_inheritedTraceOptions_2528_);
lean_inc(v_cancelTk_x3f_2526_);
lean_inc(v_currMacroScope_2524_);
lean_inc(v_quotContext_2523_);
lean_inc(v_maxHeartbeats_2522_);
lean_inc(v_initHeartbeats_2521_);
lean_inc(v_openDecls_2520_);
lean_inc(v_currNamespace_2519_);
lean_inc(v_maxRecDepth_2517_);
lean_inc(v_currRecDepth_2516_);
lean_inc_ref(v_options_2515_);
lean_inc_ref(v_fileMap_2514_);
lean_inc_ref(v_fileName_2513_);
v___x_2530_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2530_, 0, v_fileName_2513_);
lean_ctor_set(v___x_2530_, 1, v_fileMap_2514_);
lean_ctor_set(v___x_2530_, 2, v_options_2515_);
lean_ctor_set(v___x_2530_, 3, v_currRecDepth_2516_);
lean_ctor_set(v___x_2530_, 4, v_maxRecDepth_2517_);
lean_ctor_set(v___x_2530_, 5, v_ref_2529_);
lean_ctor_set(v___x_2530_, 6, v_currNamespace_2519_);
lean_ctor_set(v___x_2530_, 7, v_openDecls_2520_);
lean_ctor_set(v___x_2530_, 8, v_initHeartbeats_2521_);
lean_ctor_set(v___x_2530_, 9, v_maxHeartbeats_2522_);
lean_ctor_set(v___x_2530_, 10, v_quotContext_2523_);
lean_ctor_set(v___x_2530_, 11, v_currMacroScope_2524_);
lean_ctor_set(v___x_2530_, 12, v_cancelTk_x3f_2526_);
lean_ctor_set(v___x_2530_, 13, v_inheritedTraceOptions_2528_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*14, v_diag_2525_);
lean_ctor_set_uint8(v___x_2530_, sizeof(void*)*14 + 1, v_suppressElabErrors_2527_);
v___x_2531_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2506_, v___y_2508_, v___y_2509_, v___x_2530_, v___y_2511_);
lean_dec_ref_known(v___x_2530_, 14);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2532_, lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2532_, v_msg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec(v_ref_2532_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2541_, lean_object* v_msg_2542_, lean_object* v_declHint_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___x_2550_; lean_object* v_a_2551_; lean_object* v___x_2552_; 
v___x_2550_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2542_, v_declHint_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_a_2551_);
lean_dec_ref(v___x_2550_);
v___x_2552_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2541_, v_a_2551_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2553_, lean_object* v_msg_2554_, lean_object* v_declHint_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2553_, v_msg_2554_, v_declHint_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec(v_ref_2553_);
return v_res_2562_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2565_ = l_Lean_stringToMessageData(v___x_2564_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2568_ = l_Lean_stringToMessageData(v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2569_, lean_object* v_constName_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2577_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2578_ = 0;
lean_inc(v_constName_2570_);
v___x_2579_ = l_Lean_MessageData_ofConstName(v_constName_2570_, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2577_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2569_, v___x_2582_, v_constName_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2584_, lean_object* v_constName_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2584_, v_constName_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v_ref_2584_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_ref_2600_; lean_object* v___x_2601_; 
v_ref_2600_ = lean_ctor_get(v___y_2597_, 5);
v___x_2601_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2600_, v_constName_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v_env_2618_; uint8_t v___x_2619_; lean_object* v___x_2620_; 
v___x_2617_ = lean_st_ref_get(v___y_2615_);
v_env_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc_ref(v_env_2618_);
lean_dec(v___x_2617_);
v___x_2619_ = 0;
lean_inc(v_constName_2610_);
v___x_2620_ = l_Lean_Environment_find_x3f(v_env_2618_, v_constName_2610_, v___x_2619_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2621_;
}
else
{
lean_object* v_val_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_constName_2610_);
v_val_2622_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2620_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_val_2622_);
lean_dec(v___x_2620_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 0);
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_val_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
return v_res_2637_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2642_ = lean_unsigned_to_nat(53u);
v___x_2643_ = lean_unsigned_to_nat(62u);
v___x_2644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2646_ = l_mkPanicMessageWithDecl(v___x_2645_, v___x_2644_, v___x_2643_, v___x_2642_, v___x_2641_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2647_, size_t v_i_2648_, lean_object* v_bs_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_usize_dec_lt(v_i_2648_, v_sz_2647_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_bs_2649_);
return v___x_2657_;
}
else
{
lean_object* v_v_2658_; lean_object* v___x_2659_; 
v_v_2658_ = lean_array_uget_borrowed(v_bs_2649_, v_i_2648_);
lean_inc(v_v_2658_);
v___x_2659_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2658_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; lean_object* v_bs_x27_2662_; lean_object* v_a_2664_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = lean_unsigned_to_nat(0u);
v_bs_x27_2662_ = lean_array_uset(v_bs_2649_, v_i_2648_, v___x_2661_);
if (lean_obj_tag(v_a_2660_) == 6)
{
lean_object* v_val_2669_; lean_object* v_numFields_2670_; uint8_t v___x_2671_; lean_object* v___x_2672_; 
v_val_2669_ = lean_ctor_get(v_a_2660_, 0);
lean_inc_ref(v_val_2669_);
lean_dec_ref_known(v_a_2660_, 1);
v_numFields_2670_ = lean_ctor_get(v_val_2669_, 4);
lean_inc(v_numFields_2670_);
lean_dec_ref(v_val_2669_);
v___x_2671_ = 0;
v___x_2672_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2672_, 0, v_numFields_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2661_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*2, v___x_2671_);
v_a_2664_ = v___x_2672_;
goto v___jp_2663_;
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v_a_2660_);
v___x_2673_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2674_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2673_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v_a_2664_ = v_a_2675_;
goto v___jp_2663_;
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v_bs_x27_2662_);
v_a_2676_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2674_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
v___jp_2663_:
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = ((size_t)1ULL);
v___x_2666_ = lean_usize_add(v_i_2648_, v___x_2665_);
v___x_2667_ = lean_array_uset(v_bs_x27_2662_, v_i_2648_, v_a_2664_);
v_i_2648_ = v___x_2666_;
v_bs_2649_ = v___x_2667_;
goto _start;
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec_ref(v_bs_2649_);
v_a_2684_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2659_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2659_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2692_, lean_object* v_i_2693_, lean_object* v_bs_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
size_t v_sz_boxed_2701_; size_t v_i_boxed_2702_; lean_object* v_res_2703_; 
v_sz_boxed_2701_ = lean_unbox_usize(v_sz_2692_);
lean_dec(v_sz_2692_);
v_i_boxed_2702_ = lean_unbox_usize(v_i_2693_);
lean_dec(v_i_2693_);
v_res_2703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2701_, v_i_boxed_2702_, v_bs_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
return v_res_2703_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = lean_box(0);
v___x_2705_ = lean_unsigned_to_nat(16u);
v___x_2706_ = lean_mk_array(v___x_2705_, v___x_2704_);
return v___x_2706_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2708_ = lean_unsigned_to_nat(0u);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
lean_ctor_set(v___x_2709_, 1, v___x_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2712_, uint8_t v_alsoCasesOn_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
uint8_t v___x_2723_; 
v___x_2723_ = l_Lean_Expr_isApp(v_e_2712_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref(v_e_2712_);
v___x_2724_ = lean_box(0);
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
return v___x_2725_;
}
else
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_Expr_getAppFn(v_e_2712_);
if (lean_obj_tag(v___x_2726_) == 4)
{
lean_object* v_declName_2727_; lean_object* v_us_2728_; lean_object* v___x_2729_; lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2884_; 
v_declName_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc_n(v_declName_2727_, 2);
v_us_2728_ = lean_ctor_get(v___x_2726_, 1);
lean_inc(v_us_2728_);
lean_dec_ref_known(v___x_2726_, 2);
v___x_2729_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2727_, v___y_2718_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2884_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2884_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
if (lean_obj_tag(v_a_2730_) == 1)
{
lean_object* v_val_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2776_; 
v_val_2734_ = lean_ctor_get(v_a_2730_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_a_2730_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2736_ = v_a_2730_;
v_isShared_2737_ = v_isSharedCheck_2776_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_val_2734_);
lean_dec(v_a_2730_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2776_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v_dummy_2738_; lean_object* v_nargs_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v_args_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; 
v_dummy_2738_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2739_ = l_Lean_Expr_getAppNumArgs(v_e_2712_);
lean_inc(v_nargs_2739_);
v___x_2740_ = lean_mk_array(v_nargs_2739_, v_dummy_2738_);
v___x_2741_ = lean_unsigned_to_nat(1u);
v___x_2742_ = lean_nat_sub(v_nargs_2739_, v___x_2741_);
lean_dec(v_nargs_2739_);
v_args_2743_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2712_, v___x_2740_, v___x_2742_);
v___x_2744_ = lean_array_get_size(v_args_2743_);
v___x_2745_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2734_);
v___x_2746_ = lean_nat_dec_lt(v___x_2744_, v___x_2745_);
lean_dec(v___x_2745_);
if (v___x_2746_ == 0)
{
lean_object* v_numParams_2747_; lean_object* v_numDiscrs_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v_numParams_2747_ = lean_ctor_get(v_val_2734_, 0);
v_numDiscrs_2748_ = lean_ctor_get(v_val_2734_, 1);
v___x_2749_ = lean_array_mk(v_us_2728_);
v___x_2750_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2747_);
v___x_2751_ = l_Array_extract___redArg(v_args_2743_, v___x_2750_, v_numParams_2747_);
v___x_2752_ = l_Lean_instInhabitedExpr;
v___x_2753_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2734_);
v___x_2754_ = lean_array_get(v___x_2752_, v_args_2743_, v___x_2753_);
lean_dec(v___x_2753_);
v___x_2755_ = lean_nat_add(v_numParams_2747_, v___x_2741_);
v___x_2756_ = lean_nat_add(v___x_2755_, v_numDiscrs_2748_);
lean_inc(v___x_2756_);
lean_inc_ref_n(v_args_2743_, 2);
v___x_2757_ = l_Array_toSubarray___redArg(v_args_2743_, v___x_2755_, v___x_2756_);
v___x_2758_ = l_Subarray_copy___redArg(v___x_2757_);
v___x_2759_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2734_);
v___x_2760_ = lean_nat_add(v___x_2756_, v___x_2759_);
lean_dec(v___x_2759_);
lean_inc(v___x_2760_);
v___x_2761_ = l_Array_toSubarray___redArg(v_args_2743_, v___x_2756_, v___x_2760_);
v___x_2762_ = l_Subarray_copy___redArg(v___x_2761_);
v___x_2763_ = l_Array_toSubarray___redArg(v_args_2743_, v___x_2760_, v___x_2744_);
v___x_2764_ = l_Subarray_copy___redArg(v___x_2763_);
v___x_2765_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2765_, 0, v_val_2734_);
lean_ctor_set(v___x_2765_, 1, v_declName_2727_);
lean_ctor_set(v___x_2765_, 2, v___x_2749_);
lean_ctor_set(v___x_2765_, 3, v___x_2751_);
lean_ctor_set(v___x_2765_, 4, v___x_2754_);
lean_ctor_set(v___x_2765_, 5, v___x_2758_);
lean_ctor_set(v___x_2765_, 6, v___x_2762_);
lean_ctor_set(v___x_2765_, 7, v___x_2764_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 0, v___x_2765_);
v___x_2767_ = v___x_2736_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2769_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2767_);
v___x_2769_ = v___x_2732_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec_ref(v_args_2743_);
lean_del_object(v___x_2736_);
lean_dec(v_val_2734_);
lean_dec(v_us_2728_);
lean_dec(v_declName_2727_);
v___x_2772_ = lean_box(0);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2772_);
v___x_2774_ = v___x_2732_;
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
}
}
else
{
lean_object* v___x_2777_; 
lean_del_object(v___x_2732_);
lean_dec(v_a_2730_);
v___x_2777_ = lean_st_ref_get(v___y_2718_);
if (v_alsoCasesOn_2713_ == 0)
{
lean_dec(v___x_2777_);
lean_dec(v_us_2728_);
lean_dec(v_declName_2727_);
lean_dec_ref(v_e_2712_);
goto v___jp_2720_;
}
else
{
lean_object* v_env_2778_; uint8_t v___x_2779_; 
v_env_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc_ref(v_env_2778_);
lean_dec(v___x_2777_);
lean_inc(v_declName_2727_);
v___x_2779_ = l_Lean_isCasesOnRecursor(v_env_2778_, v_declName_2727_);
if (v___x_2779_ == 0)
{
lean_dec(v_us_2728_);
lean_dec(v_declName_2727_);
lean_dec_ref(v_e_2712_);
goto v___jp_2720_;
}
else
{
lean_object* v_indName_2780_; lean_object* v___x_2781_; 
v_indName_2780_ = l_Lean_Name_getPrefix(v_declName_2727_);
v___x_2781_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2780_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2875_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2875_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2875_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
if (lean_obj_tag(v_a_2782_) == 5)
{
lean_object* v_val_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2870_; 
v_val_2786_ = lean_ctor_get(v_a_2782_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_a_2782_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2788_ = v_a_2782_;
v_isShared_2789_ = v_isSharedCheck_2870_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_val_2786_);
lean_dec(v_a_2782_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2870_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v_toConstantVal_2790_; lean_object* v_numParams_2791_; lean_object* v_numIndices_2792_; lean_object* v_ctors_2793_; lean_object* v_nargs_2794_; lean_object* v_dummy_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v_args_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v_toConstantVal_2790_ = lean_ctor_get(v_val_2786_, 0);
lean_inc_ref(v_toConstantVal_2790_);
v_numParams_2791_ = lean_ctor_get(v_val_2786_, 1);
lean_inc(v_numParams_2791_);
v_numIndices_2792_ = lean_ctor_get(v_val_2786_, 2);
lean_inc(v_numIndices_2792_);
v_ctors_2793_ = lean_ctor_get(v_val_2786_, 4);
lean_inc(v_ctors_2793_);
v_nargs_2794_ = l_Lean_Expr_getAppNumArgs(v_e_2712_);
v_dummy_2795_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2794_);
v___x_2796_ = lean_mk_array(v_nargs_2794_, v_dummy_2795_);
v___x_2797_ = lean_unsigned_to_nat(1u);
v___x_2798_ = lean_nat_sub(v_nargs_2794_, v___x_2797_);
lean_dec(v_nargs_2794_);
v_args_2799_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2712_, v___x_2796_, v___x_2798_);
v___x_2800_ = lean_nat_add(v_numParams_2791_, v___x_2797_);
v___x_2801_ = lean_nat_add(v___x_2800_, v_numIndices_2792_);
v___x_2802_ = lean_nat_add(v___x_2801_, v___x_2797_);
lean_dec(v___x_2801_);
v___x_2803_ = l_Lean_InductiveVal_numCtors(v_val_2786_);
lean_dec_ref(v_val_2786_);
v___x_2804_ = lean_nat_add(v___x_2802_, v___x_2803_);
lean_dec(v___x_2803_);
v___x_2805_ = lean_array_get_size(v_args_2799_);
v___x_2806_ = lean_nat_dec_le(v___x_2804_, v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; lean_object* v___x_2809_; 
lean_dec(v___x_2804_);
lean_dec(v___x_2802_);
lean_dec(v___x_2800_);
lean_dec_ref(v_args_2799_);
lean_dec(v_ctors_2793_);
lean_dec(v_numIndices_2792_);
lean_dec(v_numParams_2791_);
lean_dec_ref(v_toConstantVal_2790_);
lean_del_object(v___x_2788_);
lean_dec(v_us_2728_);
lean_dec(v_declName_2727_);
v___x_2807_ = lean_box(0);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2807_);
v___x_2809_ = v___x_2784_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v___x_2807_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
else
{
lean_object* v___x_2811_; lean_object* v_params_2812_; lean_object* v___x_2813_; lean_object* v_motive_2814_; lean_object* v_discrs_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v_discrInfos_2818_; lean_object* v_alts_2819_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v_lower_2861_; lean_object* v_upper_2862_; uint8_t v___x_2869_; 
lean_del_object(v___x_2784_);
v___x_2811_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2791_);
lean_inc_ref_n(v_args_2799_, 3);
v_params_2812_ = l_Array_toSubarray___redArg(v_args_2799_, v___x_2811_, v_numParams_2791_);
v___x_2813_ = l_Lean_instInhabitedExpr;
v_motive_2814_ = lean_array_get(v___x_2813_, v_args_2799_, v_numParams_2791_);
lean_dec(v_numParams_2791_);
lean_inc(v___x_2802_);
v_discrs_2815_ = l_Array_toSubarray___redArg(v_args_2799_, v___x_2800_, v___x_2802_);
v___x_2816_ = lean_nat_add(v_numIndices_2792_, v___x_2797_);
lean_dec(v_numIndices_2792_);
v___x_2817_ = lean_box(0);
v_discrInfos_2818_ = lean_mk_array(v___x_2816_, v___x_2817_);
lean_inc(v___x_2804_);
v_alts_2819_ = l_Array_toSubarray___redArg(v_args_2799_, v___x_2802_, v___x_2804_);
v___x_2869_ = lean_nat_dec_le(v___x_2804_, v___x_2811_);
if (v___x_2869_ == 0)
{
v_lower_2861_ = v___x_2804_;
v_upper_2862_ = v___x_2805_;
goto v___jp_2860_;
}
else
{
lean_dec(v___x_2804_);
v_lower_2861_ = v___x_2811_;
v_upper_2862_ = v___x_2805_;
goto v___jp_2860_;
}
v___jp_2820_:
{
lean_object* v___x_2823_; size_t v_sz_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
v___x_2823_ = lean_array_mk(v_ctors_2793_);
v_sz_2824_ = lean_array_size(v___x_2823_);
v___x_2825_ = ((size_t)0ULL);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2824_, v___x_2825_, v___x_2823_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2851_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2851_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2851_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v_start_2831_; lean_object* v_stop_2832_; lean_object* v_start_2833_; lean_object* v_stop_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v_start_2831_ = lean_ctor_get(v_params_2812_, 1);
lean_inc(v_start_2831_);
v_stop_2832_ = lean_ctor_get(v_params_2812_, 2);
lean_inc(v_stop_2832_);
v_start_2833_ = lean_ctor_get(v_discrs_2815_, 1);
lean_inc(v_start_2833_);
v_stop_2834_ = lean_ctor_get(v_discrs_2815_, 2);
lean_inc(v_stop_2834_);
v___x_2835_ = lean_nat_sub(v_stop_2832_, v_start_2831_);
lean_dec(v_start_2831_);
lean_dec(v_stop_2832_);
v___x_2836_ = lean_nat_sub(v_stop_2834_, v_start_2833_);
lean_dec(v_start_2833_);
lean_dec(v_stop_2834_);
v___x_2837_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2838_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2836_);
lean_ctor_set(v___x_2838_, 2, v_a_2827_);
lean_ctor_set(v___x_2838_, 3, v___y_2822_);
lean_ctor_set(v___x_2838_, 4, v_discrInfos_2818_);
lean_ctor_set(v___x_2838_, 5, v___x_2837_);
v___x_2839_ = lean_array_mk(v_us_2728_);
v___x_2840_ = l_Subarray_copy___redArg(v_params_2812_);
v___x_2841_ = l_Subarray_copy___redArg(v_discrs_2815_);
v___x_2842_ = l_Subarray_copy___redArg(v_alts_2819_);
v___x_2843_ = l_Subarray_copy___redArg(v___y_2821_);
v___x_2844_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2838_);
lean_ctor_set(v___x_2844_, 1, v_declName_2727_);
lean_ctor_set(v___x_2844_, 2, v___x_2839_);
lean_ctor_set(v___x_2844_, 3, v___x_2840_);
lean_ctor_set(v___x_2844_, 4, v_motive_2814_);
lean_ctor_set(v___x_2844_, 5, v___x_2841_);
lean_ctor_set(v___x_2844_, 6, v___x_2842_);
lean_ctor_set(v___x_2844_, 7, v___x_2843_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set_tag(v___x_2788_, 1);
lean_ctor_set(v___x_2788_, 0, v___x_2844_);
v___x_2846_ = v___x_2788_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2848_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2846_);
v___x_2848_ = v___x_2829_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
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
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v_alts_2819_);
lean_dec_ref(v_discrInfos_2818_);
lean_dec_ref(v_discrs_2815_);
lean_dec(v_motive_2814_);
lean_dec_ref(v_params_2812_);
lean_del_object(v___x_2788_);
lean_dec(v_us_2728_);
lean_dec(v_declName_2727_);
v_a_2852_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2826_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2826_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
v___jp_2860_:
{
lean_object* v_levelParams_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_levelParams_2863_ = lean_ctor_get(v_toConstantVal_2790_, 1);
lean_inc(v_levelParams_2863_);
lean_dec_ref(v_toConstantVal_2790_);
v___x_2864_ = l_Array_toSubarray___redArg(v_args_2799_, v_lower_2861_, v_upper_2862_);
v___x_2865_ = l_List_lengthTR___redArg(v_levelParams_2863_);
lean_dec(v_levelParams_2863_);
v___x_2866_ = l_List_lengthTR___redArg(v_us_2728_);
v___x_2867_ = lean_nat_dec_eq(v___x_2865_, v___x_2866_);
lean_dec(v___x_2866_);
lean_dec(v___x_2865_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; 
v___x_2868_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2821_ = v___x_2864_;
v___y_2822_ = v___x_2868_;
goto v___jp_2820_;
}
else
{
v___y_2821_ = v___x_2864_;
v___y_2822_ = v___x_2817_;
goto v___jp_2820_;
}
}
}
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
lean_dec(v_a_2782_);
lean_dec(v_us_2728_);
lean_dec(v_declName_2727_);
lean_dec_ref(v_e_2712_);
v___x_2871_ = lean_box(0);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___x_2871_);
v___x_2873_ = v___x_2784_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_us_2728_);
lean_dec(v_declName_2727_);
lean_dec_ref(v_e_2712_);
v_a_2876_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2781_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2781_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
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
lean_dec_ref(v___x_2726_);
lean_dec_ref(v_e_2712_);
goto v___jp_2720_;
}
}
v___jp_2720_:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2885_, lean_object* v_alsoCasesOn_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2893_; lean_object* v_res_2894_; 
v_alsoCasesOn_boxed_2893_ = lean_unbox(v_alsoCasesOn_2886_);
v_res_2894_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2885_, v_alsoCasesOn_boxed_2893_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
if (lean_obj_tag(v_a_2895_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = l_List_reverse___redArg(v_a_2896_);
return v___x_2897_;
}
else
{
lean_object* v_head_2898_; lean_object* v_tail_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2908_; 
v_head_2898_ = lean_ctor_get(v_a_2895_, 0);
v_tail_2899_ = lean_ctor_get(v_a_2895_, 1);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_a_2895_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2901_ = v_a_2895_;
v_isShared_2902_ = v_isSharedCheck_2908_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_tail_2899_);
lean_inc(v_head_2898_);
lean_dec(v_a_2895_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2908_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2903_ = l_Lean_MessageData_ofExpr(v_head_2898_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 1, v_a_2896_);
lean_ctor_set(v___x_2901_, 0, v___x_2903_);
v___x_2905_ = v___x_2901_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2903_);
lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_a_2896_);
v___x_2905_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
v_a_2895_ = v_tail_2899_;
v_a_2896_ = v___x_2905_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2909_, lean_object* v_x_2910_){
_start:
{
lean_object* v_fnName_2911_; uint8_t v___x_2912_; 
v_fnName_2911_ = lean_ctor_get(v_x_2910_, 0);
v___x_2912_ = l_Lean_Expr_isConstOf(v_x_2909_, v_fnName_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2913_, lean_object* v_x_2914_){
_start:
{
uint8_t v_res_2915_; lean_object* v_r_2916_; 
v_res_2915_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2913_, v_x_2914_);
lean_dec_ref(v_x_2914_);
lean_dec_ref(v_x_2913_);
v_r_2916_ = lean_box(v_res_2915_);
return v_r_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2917_, lean_object* v_type_2918_, lean_object* v_val_2919_, lean_object* v_k_2920_, uint8_t v_nondep_2921_, uint8_t v_kind_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___f_2929_; lean_object* v___x_2930_; 
lean_inc(v___y_2923_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2929_, 0, v_k_2920_);
lean_closure_set(v___f_2929_, 1, v___y_2923_);
v___x_2930_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2917_, v_type_2918_, v_val_2919_, v___f_2929_, v_nondep_2921_, v_kind_2922_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
if (lean_obj_tag(v___x_2930_) == 0)
{
return v___x_2930_;
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2939_, lean_object* v_type_2940_, lean_object* v_val_2941_, lean_object* v_k_2942_, lean_object* v_nondep_2943_, lean_object* v_kind_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
uint8_t v_nondep_boxed_2951_; uint8_t v_kind_boxed_2952_; lean_object* v_res_2953_; 
v_nondep_boxed_2951_ = lean_unbox(v_nondep_2943_);
v_kind_boxed_2952_ = lean_unbox(v_kind_2944_);
v_res_2953_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2939_, v_type_2940_, v_val_2941_, v_k_2942_, v_nondep_boxed_2951_, v_kind_boxed_2952_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2954_, uint8_t v_usedLetOnly_2955_, lean_object* v_x_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; 
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
lean_inc(v___y_2957_);
lean_inc_ref(v_x_2956_);
v___x_2963_ = lean_apply_7(v_k_2954_, v_x_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, lean_box(0));
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; uint8_t v___x_2969_; lean_object* v___x_2970_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = lean_unsigned_to_nat(1u);
v___x_2966_ = lean_mk_empty_array_with_capacity(v___x_2965_);
v___x_2967_ = lean_array_push(v___x_2966_, v_x_2956_);
v___x_2968_ = 0;
v___x_2969_ = 1;
v___x_2970_ = l_Lean_Meta_mkLetFVars(v___x_2967_, v_a_2964_, v_usedLetOnly_2955_, v___x_2968_, v___x_2969_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec_ref(v___x_2967_);
return v___x_2970_;
}
else
{
lean_dec_ref(v_x_2956_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2971_, lean_object* v_usedLetOnly_2972_, lean_object* v_x_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
uint8_t v_usedLetOnly_boxed_2980_; lean_object* v_res_2981_; 
v_usedLetOnly_boxed_2980_ = lean_unbox(v_usedLetOnly_2972_);
v_res_2981_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2971_, v_usedLetOnly_boxed_2980_, v_x_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2982_, lean_object* v_type_2983_, lean_object* v_val_2984_, lean_object* v_k_2985_, uint8_t v_nondep_2986_, uint8_t v_kind_2987_, uint8_t v_usedLetOnly_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v___x_2995_; lean_object* v___f_2996_; lean_object* v___x_2997_; 
v___x_2995_ = lean_box(v_usedLetOnly_2988_);
v___f_2996_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2996_, 0, v_k_2985_);
lean_closure_set(v___f_2996_, 1, v___x_2995_);
v___x_2997_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2982_, v_type_2983_, v_val_2984_, v___f_2996_, v_nondep_2986_, v_kind_2987_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2998_, lean_object* v_type_2999_, lean_object* v_val_3000_, lean_object* v_k_3001_, lean_object* v_nondep_3002_, lean_object* v_kind_3003_, lean_object* v_usedLetOnly_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_){
_start:
{
uint8_t v_nondep_boxed_3011_; uint8_t v_kind_boxed_3012_; uint8_t v_usedLetOnly_boxed_3013_; lean_object* v_res_3014_; 
v_nondep_boxed_3011_ = lean_unbox(v_nondep_3002_);
v_kind_boxed_3012_ = lean_unbox(v_kind_3003_);
v_usedLetOnly_boxed_3013_ = lean_unbox(v_usedLetOnly_3004_);
v_res_3014_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2998_, v_type_2999_, v_val_3000_, v_k_3001_, v_nondep_boxed_3011_, v_kind_boxed_3012_, v_usedLetOnly_boxed_3013_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
return v_res_3014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3015_, lean_object* v_positions_3016_, lean_object* v_recFnNames_3017_, lean_object* v_containsRecFn_3018_, lean_object* v_below_3019_, size_t v_sz_3020_, size_t v_i_3021_, lean_object* v_bs_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_usize_dec_lt(v_i_3021_, v_sz_3020_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_dec_ref(v_below_3019_);
lean_dec_ref(v_containsRecFn_3018_);
lean_dec_ref(v_recFnNames_3017_);
lean_dec_ref(v_positions_3016_);
lean_dec_ref(v_recArgInfos_3015_);
v___x_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3030_, 0, v_bs_3022_);
return v___x_3030_;
}
else
{
lean_object* v_v_3031_; lean_object* v___x_3032_; 
v_v_3031_ = lean_array_uget_borrowed(v_bs_3022_, v_i_3021_);
lean_inc_ref(v___y_3026_);
lean_inc(v_v_3031_);
lean_inc_ref(v_below_3019_);
lean_inc_ref(v_containsRecFn_3018_);
lean_inc_ref(v_recFnNames_3017_);
lean_inc_ref(v_positions_3016_);
lean_inc_ref(v_recArgInfos_3015_);
v___x_3032_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3015_, v_positions_3016_, v_recFnNames_3017_, v_containsRecFn_3018_, v_below_3019_, v_v_3031_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v_bs_x27_3035_; size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = lean_unsigned_to_nat(0u);
v_bs_x27_3035_ = lean_array_uset(v_bs_3022_, v_i_3021_, v___x_3034_);
v___x_3036_ = ((size_t)1ULL);
v___x_3037_ = lean_usize_add(v_i_3021_, v___x_3036_);
v___x_3038_ = lean_array_uset(v_bs_x27_3035_, v_i_3021_, v_a_3033_);
v_i_3021_ = v___x_3037_;
v_bs_3022_ = v___x_3038_;
goto _start;
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v_bs_3022_);
lean_dec_ref(v_below_3019_);
lean_dec_ref(v_containsRecFn_3018_);
lean_dec_ref(v_recFnNames_3017_);
lean_dec_ref(v_positions_3016_);
lean_dec_ref(v_recArgInfos_3015_);
v_a_3040_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3032_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3032_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3050_ = l_Lean_stringToMessageData(v___x_3049_);
return v___x_3050_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3053_ = l_Lean_stringToMessageData(v___x_3052_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3054_, lean_object* v_positions_3055_, lean_object* v_recFnNames_3056_, lean_object* v_containsRecFn_3057_, lean_object* v_below_3058_, lean_object* v_e_3059_, lean_object* v_x_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
if (lean_obj_tag(v_x_3060_) == 5)
{
lean_object* v_fn_3069_; lean_object* v_arg_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_fn_3069_ = lean_ctor_get(v_x_3060_, 0);
lean_inc_ref(v_fn_3069_);
v_arg_3070_ = lean_ctor_get(v_x_3060_, 1);
lean_inc_ref(v_arg_3070_);
lean_dec_ref_known(v_x_3060_, 2);
v___x_3071_ = lean_array_set(v_x_3061_, v_x_3062_, v_arg_3070_);
v___x_3072_ = lean_unsigned_to_nat(1u);
v___x_3073_ = lean_nat_sub(v_x_3062_, v___x_3072_);
lean_dec(v_x_3062_);
v_x_3060_ = v_fn_3069_;
v_x_3061_ = v___x_3071_;
v_x_3062_ = v___x_3073_;
goto _start;
}
else
{
lean_object* v___f_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_dec(v_x_3062_);
lean_inc_ref(v_x_3060_);
v___f_3075_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3075_, 0, v_x_3060_);
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3075_, v_recArgInfos_3054_, v___x_3076_);
if (lean_obj_tag(v___x_3077_) == 1)
{
lean_object* v_val_3078_; lean_object* v___x_3079_; lean_object* v___y_3081_; lean_object* v_recArgPos_3107_; lean_object* v_indGroupInst_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
lean_dec_ref(v_x_3060_);
v_val_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_val_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = lean_array_fget_borrowed(v_recArgInfos_3054_, v_val_3078_);
v_recArgPos_3107_ = lean_ctor_get(v___x_3079_, 2);
v_indGroupInst_3108_ = lean_ctor_get(v___x_3079_, 4);
v___x_3109_ = lean_array_get_size(v_x_3061_);
v___x_3110_ = lean_nat_dec_lt(v_recArgPos_3107_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v_val_3078_);
lean_dec_ref(v_x_3061_);
lean_dec_ref(v_below_3058_);
lean_dec_ref(v_containsRecFn_3057_);
lean_dec_ref(v_recFnNames_3056_);
lean_dec_ref(v_positions_3055_);
lean_dec_ref(v_recArgInfos_3054_);
v___x_3111_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3112_ = l_Lean_indentExpr(v_e_3059_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3113_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
return v___x_3114_;
}
else
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = lean_array_fget_borrowed(v_x_3061_, v_recArgPos_3107_);
lean_inc_ref(v___y_3066_);
lean_inc(v___x_3115_);
lean_inc_ref(v_below_3058_);
lean_inc_ref(v_containsRecFn_3057_);
lean_inc_ref(v_recFnNames_3056_);
lean_inc_ref(v_positions_3055_);
lean_inc_ref(v_recArgInfos_3054_);
v___x_3116_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3054_, v_positions_3055_, v_recFnNames_3056_, v_containsRecFn_3057_, v_below_3058_, v___x_3115_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v_params_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v_params_3118_ = lean_ctor_get(v_indGroupInst_3108_, 2);
v___x_3119_ = lean_array_get_size(v_params_3118_);
lean_inc_ref(v_positions_3055_);
lean_inc_ref(v_below_3058_);
v___x_3120_ = l_Lean_Elab_Structural_toBelow(v_below_3058_, v___x_3119_, v_positions_3055_, v_val_3078_, v_a_3117_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_dec_ref(v_e_3059_);
v___y_3081_ = v___x_3120_;
goto v___jp_3080_;
}
else
{
lean_object* v_a_3121_; uint8_t v___y_3123_; uint8_t v___x_3128_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
v___x_3128_ = l_Lean_Exception_isInterrupt(v_a_3121_);
if (v___x_3128_ == 0)
{
uint8_t v___x_3129_; 
v___x_3129_ = l_Lean_Exception_isRuntime(v_a_3121_);
v___y_3123_ = v___x_3129_;
goto v___jp_3122_;
}
else
{
lean_dec(v_a_3121_);
v___y_3123_ = v___x_3128_;
goto v___jp_3122_;
}
v___jp_3122_:
{
if (v___y_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec_ref_known(v___x_3120_, 1);
v___x_3124_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3125_ = l_Lean_indentExpr(v_e_3059_);
v___x_3126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3124_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
v___x_3127_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3126_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
v___y_3081_ = v___x_3127_;
goto v___jp_3080_;
}
else
{
lean_dec_ref(v_e_3059_);
v___y_3081_ = v___x_3120_;
goto v___jp_3080_;
}
}
}
}
else
{
lean_dec(v_val_3078_);
lean_dec_ref(v_x_3061_);
lean_dec_ref(v_e_3059_);
lean_dec_ref(v_below_3058_);
lean_dec_ref(v_containsRecFn_3057_);
lean_dec_ref(v_recFnNames_3056_);
lean_dec_ref(v_positions_3055_);
lean_dec_ref(v_recArgInfos_3054_);
return v___x_3116_;
}
}
v___jp_3080_:
{
if (lean_obj_tag(v___y_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v_fixedParamPerm_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_snd_3086_; size_t v_sz_3087_; size_t v___x_3088_; lean_object* v___x_3089_; 
v_a_3082_ = lean_ctor_get(v___y_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___y_3081_, 1);
v_fixedParamPerm_3083_ = lean_ctor_get(v___x_3079_, 1);
v___x_3084_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3083_, v_x_3061_);
lean_dec_ref(v_x_3061_);
lean_inc(v___x_3079_);
v___x_3085_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3079_, v___x_3084_);
v_snd_3086_ = lean_ctor_get(v___x_3085_, 1);
lean_inc(v_snd_3086_);
lean_dec_ref(v___x_3085_);
v_sz_3087_ = lean_array_size(v_snd_3086_);
v___x_3088_ = ((size_t)0ULL);
v___x_3089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3054_, v_positions_3055_, v_recFnNames_3056_, v_containsRecFn_3057_, v_below_3058_, v_sz_3087_, v___x_3088_, v_snd_3086_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3098_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3098_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; lean_object* v___x_3096_; 
v___x_3094_ = l_Lean_mkAppN(v_a_3082_, v_a_3090_);
lean_dec(v_a_3090_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3094_);
v___x_3096_ = v___x_3092_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v_a_3082_);
v_a_3099_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3089_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3089_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_a_3099_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
else
{
lean_dec_ref(v_x_3061_);
lean_dec_ref(v_below_3058_);
lean_dec_ref(v_containsRecFn_3057_);
lean_dec_ref(v_recFnNames_3056_);
lean_dec_ref(v_positions_3055_);
lean_dec_ref(v_recArgInfos_3054_);
return v___y_3081_;
}
}
}
else
{
lean_object* v___x_3130_; 
lean_dec(v___x_3077_);
lean_dec_ref(v_e_3059_);
lean_inc_ref(v___y_3066_);
lean_inc_ref(v_below_3058_);
lean_inc_ref(v_containsRecFn_3057_);
lean_inc_ref(v_recFnNames_3056_);
lean_inc_ref(v_positions_3055_);
lean_inc_ref(v_recArgInfos_3054_);
v___x_3130_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3054_, v_positions_3055_, v_recFnNames_3056_, v_containsRecFn_3057_, v_below_3058_, v_x_3060_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; size_t v_sz_3132_; size_t v___x_3133_; lean_object* v___x_3134_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v_sz_3132_ = lean_array_size(v_x_3061_);
v___x_3133_ = ((size_t)0ULL);
v___x_3134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3054_, v_positions_3055_, v_recFnNames_3056_, v_containsRecFn_3057_, v_below_3058_, v_sz_3132_, v___x_3133_, v_x_3061_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3143_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3137_ = v___x_3134_;
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3134_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3143_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = l_Lean_mkAppN(v_a_3131_, v_a_3135_);
lean_dec(v_a_3135_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 0, v___x_3139_);
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3131_);
v_a_3144_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3134_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3134_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_dec_ref(v_x_3061_);
lean_dec_ref(v_below_3058_);
lean_dec_ref(v_containsRecFn_3057_);
lean_dec_ref(v_recFnNames_3056_);
lean_dec_ref(v_positions_3055_);
lean_dec_ref(v_recArgInfos_3054_);
return v___x_3130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3152_, lean_object* v_recArgInfos_3153_, lean_object* v_positions_3154_, lean_object* v_recFnNames_3155_, lean_object* v_containsRecFn_3156_, lean_object* v_below_3157_, uint8_t v___x_3158_, uint8_t v_a_3159_, lean_object* v_x_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3167_ = lean_expr_instantiate1(v_body_3152_, v_x_3160_);
lean_inc_ref(v___y_3164_);
v___x_3168_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3153_, v_positions_3154_, v_recFnNames_3155_, v_containsRecFn_3156_, v_below_3157_, v___x_3167_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; uint8_t v___x_3173_; lean_object* v___x_3174_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v___x_3170_ = lean_unsigned_to_nat(1u);
v___x_3171_ = lean_mk_empty_array_with_capacity(v___x_3170_);
v___x_3172_ = lean_array_push(v___x_3171_, v_x_3160_);
v___x_3173_ = 1;
v___x_3174_ = l_Lean_Meta_mkLambdaFVars(v___x_3172_, v_a_3169_, v___x_3158_, v_a_3159_, v___x_3158_, v_a_3159_, v___x_3173_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec_ref(v___x_3172_);
return v___x_3174_;
}
else
{
lean_dec_ref(v_x_3160_);
return v___x_3168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3175_, lean_object* v_recArgInfos_3176_, lean_object* v_positions_3177_, lean_object* v_recFnNames_3178_, lean_object* v_containsRecFn_3179_, lean_object* v_below_3180_, lean_object* v___x_3181_, lean_object* v_a_3182_, lean_object* v_x_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v___x_32812__boxed_3190_; uint8_t v_a_32813__boxed_3191_; lean_object* v_res_3192_; 
v___x_32812__boxed_3190_ = lean_unbox(v___x_3181_);
v_a_32813__boxed_3191_ = lean_unbox(v_a_3182_);
v_res_3192_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3175_, v_recArgInfos_3176_, v_positions_3177_, v_recFnNames_3178_, v_containsRecFn_3179_, v_below_3180_, v___x_32812__boxed_3190_, v_a_32813__boxed_3191_, v_x_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v_body_3175_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3193_, lean_object* v_recArgInfos_3194_, lean_object* v_positions_3195_, lean_object* v_recFnNames_3196_, lean_object* v_containsRecFn_3197_, lean_object* v_below_3198_, uint8_t v___x_3199_, uint8_t v_a_3200_, lean_object* v_x_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_expr_instantiate1(v_body_3193_, v_x_3201_);
lean_inc_ref(v___y_3205_);
v___x_3209_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3194_, v_positions_3195_, v_recFnNames_3196_, v_containsRecFn_3197_, v_below_3198_, v___x_3208_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = lean_unsigned_to_nat(1u);
v___x_3212_ = lean_mk_empty_array_with_capacity(v___x_3211_);
v___x_3213_ = lean_array_push(v___x_3212_, v_x_3201_);
v___x_3214_ = 1;
v___x_3215_ = l_Lean_Meta_mkForallFVars(v___x_3213_, v_a_3210_, v___x_3199_, v_a_3200_, v_a_3200_, v___x_3214_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec_ref(v___x_3213_);
return v___x_3215_;
}
else
{
lean_dec_ref(v_x_3201_);
return v___x_3209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3216_, lean_object* v_recArgInfos_3217_, lean_object* v_positions_3218_, lean_object* v_recFnNames_3219_, lean_object* v_containsRecFn_3220_, lean_object* v_below_3221_, lean_object* v___x_3222_, lean_object* v_a_3223_, lean_object* v_x_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v___x_32830__boxed_3231_; uint8_t v_a_32831__boxed_3232_; lean_object* v_res_3233_; 
v___x_32830__boxed_3231_ = lean_unbox(v___x_3222_);
v_a_32831__boxed_3232_ = lean_unbox(v_a_3223_);
v_res_3233_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3216_, v_recArgInfos_3217_, v_positions_3218_, v_recFnNames_3219_, v_containsRecFn_3220_, v_below_3221_, v___x_32830__boxed_3231_, v_a_32831__boxed_3232_, v_x_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v_body_3216_);
return v_res_3233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3234_, lean_object* v_recArgInfos_3235_, lean_object* v_positions_3236_, lean_object* v_recFnNames_3237_, lean_object* v_containsRecFn_3238_, lean_object* v_below_3239_, lean_object* v_x_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3234_, v_recArgInfos_3235_, v_positions_3236_, v_recFnNames_3237_, v_containsRecFn_3238_, v_below_3239_, v_x_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v_x_3240_);
lean_dec_ref(v_body_3234_);
return v_res_3247_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3255_ = l_Lean_stringToMessageData(v___x_3254_);
return v___x_3255_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3258_ = l_Lean_stringToMessageData(v___x_3257_);
return v___x_3258_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3261_ = l_Lean_stringToMessageData(v___x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v_b_3262_, lean_object* v_recArgInfos_3263_, lean_object* v_positions_3264_, lean_object* v_recFnNames_3265_, lean_object* v_containsRecFn_3266_, uint8_t v___x_3267_, uint8_t v_a_3268_, lean_object* v___x_3269_, lean_object* v_a_3270_, lean_object* v_e_3271_, lean_object* v___x_3272_, lean_object* v_xs_3273_, lean_object* v_altBody_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v_options_3317_; uint8_t v_hasTrace_3318_; 
v_options_3317_ = lean_ctor_get(v___y_3278_, 2);
v_hasTrace_3318_ = lean_ctor_get_uint8(v_options_3317_, sizeof(void*)*1);
if (v_hasTrace_3318_ == 0)
{
lean_dec(v___x_3272_);
v___y_3294_ = v___y_3275_;
v___y_3295_ = v___y_3276_;
v___y_3296_ = v___y_3277_;
v___y_3297_ = v___y_3278_;
v___y_3298_ = v___y_3279_;
goto v___jp_3293_;
}
else
{
lean_object* v_inheritedTraceOptions_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v_inheritedTraceOptions_3319_ = lean_ctor_get(v___y_3278_, 13);
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3272_);
v___x_3321_ = l_Lean_Name_append(v___x_3320_, v___x_3272_);
v___x_3322_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3319_, v_options_3317_, v___x_3321_);
lean_dec(v___x_3321_);
if (v___x_3322_ == 0)
{
lean_dec(v___x_3272_);
v___y_3294_ = v___y_3275_;
v___y_3295_ = v___y_3276_;
v___y_3296_ = v___y_3277_;
v___y_3297_ = v___y_3278_;
v___y_3298_ = v___y_3279_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3323_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3262_);
v___x_3324_ = l_Nat_reprFast(v_b_3262_);
v___x_3325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
v___x_3326_ = l_Lean_MessageData_ofFormat(v___x_3325_);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3323_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
lean_inc_ref(v_xs_3273_);
v___x_3330_ = lean_array_to_list(v_xs_3273_);
v___x_3331_ = lean_box(0);
v___x_3332_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3330_, v___x_3331_);
v___x_3333_ = l_Lean_MessageData_ofList(v___x_3332_);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3329_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3272_, v___x_3334_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_dec_ref_known(v___x_3335_, 1);
v___y_3294_ = v___y_3275_;
v___y_3295_ = v___y_3276_;
v___y_3296_ = v___y_3277_;
v___y_3297_ = v___y_3278_;
v___y_3298_ = v___y_3279_;
goto v___jp_3293_;
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_dec_ref(v_altBody_3274_);
lean_dec_ref(v_xs_3273_);
lean_dec_ref(v_e_3271_);
lean_dec_ref(v_a_3270_);
lean_dec_ref(v_containsRecFn_3266_);
lean_dec_ref(v_recFnNames_3265_);
lean_dec_ref(v_positions_3264_);
lean_dec_ref(v_recArgInfos_3263_);
lean_dec(v_b_3262_);
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
}
v___jp_3281_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = l_Lean_instInhabitedExpr;
v___x_3288_ = lean_array_get_borrowed(v___x_3287_, v_xs_3273_, v_b_3262_);
lean_dec(v_b_3262_);
lean_inc_ref(v___y_3285_);
lean_inc(v___x_3288_);
v___x_3289_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3263_, v_positions_3264_, v_recFnNames_3265_, v_containsRecFn_3266_, v___x_3288_, v_altBody_3274_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___x_3289_, 1);
v___x_3291_ = 1;
v___x_3292_ = l_Lean_Meta_mkLambdaFVars(v_xs_3273_, v_a_3290_, v___x_3267_, v_a_3268_, v___x_3267_, v_a_3268_, v___x_3291_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec_ref(v_xs_3273_);
return v___x_3292_;
}
else
{
lean_dec_ref(v_xs_3273_);
return v___x_3289_;
}
}
v___jp_3293_:
{
lean_object* v___x_3299_; uint8_t v___x_3300_; 
v___x_3299_ = lean_array_get_size(v_xs_3273_);
v___x_3300_ = lean_nat_dec_eq(v___x_3299_, v___x_3269_);
if (v___x_3300_ == 0)
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v_altBody_3274_);
lean_dec_ref(v_xs_3273_);
lean_dec_ref(v_containsRecFn_3266_);
lean_dec_ref(v_recFnNames_3265_);
lean_dec_ref(v_positions_3264_);
lean_dec_ref(v_recArgInfos_3263_);
lean_dec(v_b_3262_);
v___x_3301_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3302_ = l_Lean_indentExpr(v_a_3270_);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = l_Lean_indentExpr(v_e_3271_);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3307_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
else
{
lean_dec_ref(v_e_3271_);
lean_dec_ref(v_a_3270_);
v___y_3282_ = v___y_3294_;
v___y_3283_ = v___y_3295_;
v___y_3284_ = v___y_3296_;
v___y_3285_ = v___y_3297_;
v___y_3286_ = v___y_3298_;
goto v___jp_3281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v_b_3344_ = _args[0];
lean_object* v_recArgInfos_3345_ = _args[1];
lean_object* v_positions_3346_ = _args[2];
lean_object* v_recFnNames_3347_ = _args[3];
lean_object* v_containsRecFn_3348_ = _args[4];
lean_object* v___x_3349_ = _args[5];
lean_object* v_a_3350_ = _args[6];
lean_object* v___x_3351_ = _args[7];
lean_object* v_a_3352_ = _args[8];
lean_object* v_e_3353_ = _args[9];
lean_object* v___x_3354_ = _args[10];
lean_object* v_xs_3355_ = _args[11];
lean_object* v_altBody_3356_ = _args[12];
lean_object* v___y_3357_ = _args[13];
lean_object* v___y_3358_ = _args[14];
lean_object* v___y_3359_ = _args[15];
lean_object* v___y_3360_ = _args[16];
lean_object* v___y_3361_ = _args[17];
lean_object* v___y_3362_ = _args[18];
_start:
{
uint8_t v___x_32904__boxed_3363_; uint8_t v_a_32905__boxed_3364_; lean_object* v_res_3365_; 
v___x_32904__boxed_3363_ = lean_unbox(v___x_3349_);
v_a_32905__boxed_3364_ = lean_unbox(v_a_3350_);
v_res_3365_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v_b_3344_, v_recArgInfos_3345_, v_positions_3346_, v_recFnNames_3347_, v_containsRecFn_3348_, v___x_32904__boxed_3363_, v_a_32905__boxed_3364_, v___x_3351_, v_a_3352_, v_e_3353_, v___x_3354_, v_xs_3355_, v_altBody_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___x_3351_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3366_, lean_object* v_positions_3367_, lean_object* v_recFnNames_3368_, lean_object* v_containsRecFn_3369_, uint8_t v_a_3370_, lean_object* v_e_3371_, lean_object* v_as_3372_, lean_object* v_bs_3373_, lean_object* v_i_3374_, lean_object* v_cs_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3382_ = lean_array_get_size(v_as_3372_);
v___x_3383_ = lean_nat_dec_lt(v_i_3374_, v___x_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; 
lean_dec(v_i_3374_);
lean_dec_ref(v_e_3371_);
lean_dec_ref(v_containsRecFn_3369_);
lean_dec_ref(v_recFnNames_3368_);
lean_dec_ref(v_positions_3367_);
lean_dec_ref(v_recArgInfos_3366_);
v___x_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_cs_3375_);
return v___x_3384_;
}
else
{
lean_object* v___x_3385_; uint8_t v___x_3386_; 
v___x_3385_ = lean_array_get_size(v_bs_3373_);
v___x_3386_ = lean_nat_dec_lt(v_i_3374_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; 
lean_dec(v_i_3374_);
lean_dec_ref(v_e_3371_);
lean_dec_ref(v_containsRecFn_3369_);
lean_dec_ref(v_recFnNames_3368_);
lean_dec_ref(v_positions_3367_);
lean_dec_ref(v_recArgInfos_3366_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_cs_3375_);
return v___x_3387_;
}
else
{
uint8_t v___x_3388_; lean_object* v___x_3389_; lean_object* v_a_3390_; lean_object* v_b_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___f_3396_; lean_object* v___x_3397_; 
v___x_3388_ = 0;
v___x_3389_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3390_ = lean_array_fget_borrowed(v_as_3372_, v_i_3374_);
v_b_3391_ = lean_array_fget_borrowed(v_bs_3373_, v_i_3374_);
v___x_3392_ = lean_unsigned_to_nat(1u);
v___x_3393_ = lean_nat_add(v_b_3391_, v___x_3392_);
v___x_3394_ = lean_box(v___x_3388_);
v___x_3395_ = lean_box(v_a_3370_);
lean_inc_ref(v_e_3371_);
lean_inc_n(v_a_3390_, 2);
lean_inc(v___x_3393_);
lean_inc_ref(v_containsRecFn_3369_);
lean_inc_ref(v_recFnNames_3368_);
lean_inc_ref(v_positions_3367_);
lean_inc_ref(v_recArgInfos_3366_);
lean_inc(v_b_3391_);
v___f_3396_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 19, 11);
lean_closure_set(v___f_3396_, 0, v_b_3391_);
lean_closure_set(v___f_3396_, 1, v_recArgInfos_3366_);
lean_closure_set(v___f_3396_, 2, v_positions_3367_);
lean_closure_set(v___f_3396_, 3, v_recFnNames_3368_);
lean_closure_set(v___f_3396_, 4, v_containsRecFn_3369_);
lean_closure_set(v___f_3396_, 5, v___x_3394_);
lean_closure_set(v___f_3396_, 6, v___x_3395_);
lean_closure_set(v___f_3396_, 7, v___x_3393_);
lean_closure_set(v___f_3396_, 8, v_a_3390_);
lean_closure_set(v___f_3396_, 9, v_e_3371_);
lean_closure_set(v___f_3396_, 10, v___x_3389_);
v___x_3397_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3390_, v___x_3393_, v___f_3396_, v___x_3388_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3397_, 1);
v___x_3399_ = lean_nat_add(v_i_3374_, v___x_3392_);
lean_dec(v_i_3374_);
v___x_3400_ = lean_array_push(v_cs_3375_, v_a_3398_);
v_i_3374_ = v___x_3399_;
v_cs_3375_ = v___x_3400_;
goto _start;
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v_cs_3375_);
lean_dec(v_i_3374_);
lean_dec_ref(v_e_3371_);
lean_dec_ref(v_containsRecFn_3369_);
lean_dec_ref(v_recFnNames_3368_);
lean_dec_ref(v_positions_3367_);
lean_dec_ref(v_recArgInfos_3366_);
v_a_3402_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3397_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3397_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
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
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3412_ = l_Lean_stringToMessageData(v___x_3411_);
return v___x_3412_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3415_ = l_Lean_stringToMessageData(v___x_3414_);
return v___x_3415_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3417_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3418_ = l_Lean_stringToMessageData(v___x_3417_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3419_, lean_object* v_positions_3420_, lean_object* v_recFnNames_3421_, lean_object* v_containsRecFn_3422_, lean_object* v_below_3423_, lean_object* v_e_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v_e_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___x_3444_; 
lean_inc_ref(v_containsRecFn_3422_);
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3427_);
lean_inc_ref(v_a_3426_);
lean_inc(v_a_3425_);
lean_inc_ref(v_e_3424_);
v___x_3444_ = lean_apply_7(v_containsRecFn_3422_, v_e_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, lean_box(0));
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3667_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3667_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3667_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
uint8_t v___x_3449_; 
v___x_3449_ = lean_unbox(v_a_3445_);
if (v___x_3449_ == 0)
{
lean_object* v___x_3451_; 
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v_e_3424_);
v___x_3451_ = v___x_3447_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_e_3424_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
else
{
uint8_t v___x_3453_; 
lean_del_object(v___x_3447_);
v___x_3453_ = 0;
switch(lean_obj_tag(v_e_3424_))
{
case 6:
{
lean_object* v_binderName_3454_; lean_object* v_binderType_3455_; lean_object* v_body_3456_; uint8_t v_binderInfo_3457_; lean_object* v___x_3458_; 
v_binderName_3454_ = lean_ctor_get(v_e_3424_, 0);
lean_inc(v_binderName_3454_);
v_binderType_3455_ = lean_ctor_get(v_e_3424_, 1);
lean_inc_ref(v_binderType_3455_);
v_body_3456_ = lean_ctor_get(v_e_3424_, 2);
lean_inc_ref(v_body_3456_);
v_binderInfo_3457_ = lean_ctor_get_uint8(v_e_3424_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3424_, 3);
lean_inc_ref(v_a_3428_);
lean_inc_ref(v_below_3423_);
lean_inc_ref(v_containsRecFn_3422_);
lean_inc_ref(v_recFnNames_3421_);
lean_inc_ref(v_positions_3420_);
lean_inc_ref(v_recArgInfos_3419_);
v___x_3458_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v_below_3423_, v_binderType_3455_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3460_; lean_object* v___f_3461_; uint8_t v___x_3462_; lean_object* v___x_3463_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___x_3460_ = lean_box(v___x_3453_);
v___f_3461_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3461_, 0, v_body_3456_);
lean_closure_set(v___f_3461_, 1, v_recArgInfos_3419_);
lean_closure_set(v___f_3461_, 2, v_positions_3420_);
lean_closure_set(v___f_3461_, 3, v_recFnNames_3421_);
lean_closure_set(v___f_3461_, 4, v_containsRecFn_3422_);
lean_closure_set(v___f_3461_, 5, v_below_3423_);
lean_closure_set(v___f_3461_, 6, v___x_3460_);
lean_closure_set(v___f_3461_, 7, v_a_3445_);
v___x_3462_ = 0;
v___x_3463_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3454_, v_binderInfo_3457_, v_a_3459_, v___f_3461_, v___x_3462_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
lean_dec_ref(v_a_3428_);
return v___x_3463_;
}
else
{
lean_dec_ref(v_body_3456_);
lean_dec(v_binderName_3454_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
return v___x_3458_;
}
}
case 7:
{
lean_object* v_binderName_3464_; lean_object* v_binderType_3465_; lean_object* v_body_3466_; uint8_t v_binderInfo_3467_; lean_object* v___x_3468_; 
v_binderName_3464_ = lean_ctor_get(v_e_3424_, 0);
lean_inc(v_binderName_3464_);
v_binderType_3465_ = lean_ctor_get(v_e_3424_, 1);
lean_inc_ref(v_binderType_3465_);
v_body_3466_ = lean_ctor_get(v_e_3424_, 2);
lean_inc_ref(v_body_3466_);
v_binderInfo_3467_ = lean_ctor_get_uint8(v_e_3424_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3424_, 3);
lean_inc_ref(v_a_3428_);
lean_inc_ref(v_below_3423_);
lean_inc_ref(v_containsRecFn_3422_);
lean_inc_ref(v_recFnNames_3421_);
lean_inc_ref(v_positions_3420_);
lean_inc_ref(v_recArgInfos_3419_);
v___x_3468_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v_below_3423_, v_binderType_3465_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v_a_3469_; lean_object* v___x_3470_; lean_object* v___f_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; 
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
lean_dec_ref_known(v___x_3468_, 1);
v___x_3470_ = lean_box(v___x_3453_);
v___f_3471_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3471_, 0, v_body_3466_);
lean_closure_set(v___f_3471_, 1, v_recArgInfos_3419_);
lean_closure_set(v___f_3471_, 2, v_positions_3420_);
lean_closure_set(v___f_3471_, 3, v_recFnNames_3421_);
lean_closure_set(v___f_3471_, 4, v_containsRecFn_3422_);
lean_closure_set(v___f_3471_, 5, v_below_3423_);
lean_closure_set(v___f_3471_, 6, v___x_3470_);
lean_closure_set(v___f_3471_, 7, v_a_3445_);
v___x_3472_ = 0;
v___x_3473_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3464_, v_binderInfo_3467_, v_a_3469_, v___f_3471_, v___x_3472_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
lean_dec_ref(v_a_3428_);
return v___x_3473_;
}
else
{
lean_dec_ref(v_body_3466_);
lean_dec(v_binderName_3464_);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
return v___x_3468_;
}
}
case 8:
{
lean_object* v_declName_3474_; lean_object* v_type_3475_; lean_object* v_value_3476_; lean_object* v_body_3477_; uint8_t v_nondep_3478_; lean_object* v___x_3479_; 
lean_dec(v_a_3445_);
v_declName_3474_ = lean_ctor_get(v_e_3424_, 0);
lean_inc(v_declName_3474_);
v_type_3475_ = lean_ctor_get(v_e_3424_, 1);
lean_inc_ref(v_type_3475_);
v_value_3476_ = lean_ctor_get(v_e_3424_, 2);
lean_inc_ref(v_value_3476_);
v_body_3477_ = lean_ctor_get(v_e_3424_, 3);
lean_inc_ref(v_body_3477_);
v_nondep_3478_ = lean_ctor_get_uint8(v_e_3424_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3424_, 4);
lean_inc_ref(v_a_3428_);
lean_inc_ref(v_below_3423_);
lean_inc_ref(v_containsRecFn_3422_);
lean_inc_ref(v_recFnNames_3421_);
lean_inc_ref(v_positions_3420_);
lean_inc_ref(v_recArgInfos_3419_);
v___x_3479_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v_below_3423_, v_type_3475_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
lean_inc_ref(v_a_3428_);
lean_inc_ref(v_below_3423_);
lean_inc_ref(v_containsRecFn_3422_);
lean_inc_ref(v_recFnNames_3421_);
lean_inc_ref(v_positions_3420_);
lean_inc_ref(v_recArgInfos_3419_);
v___x_3481_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v_below_3423_, v_value_3476_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___f_3483_; uint8_t v___x_3484_; lean_object* v___x_3485_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
lean_inc(v_a_3482_);
lean_dec_ref_known(v___x_3481_, 1);
v___f_3483_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3483_, 0, v_body_3477_);
lean_closure_set(v___f_3483_, 1, v_recArgInfos_3419_);
lean_closure_set(v___f_3483_, 2, v_positions_3420_);
lean_closure_set(v___f_3483_, 3, v_recFnNames_3421_);
lean_closure_set(v___f_3483_, 4, v_containsRecFn_3422_);
lean_closure_set(v___f_3483_, 5, v_below_3423_);
v___x_3484_ = 0;
v___x_3485_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3474_, v_a_3480_, v_a_3482_, v___f_3483_, v_nondep_3478_, v___x_3484_, v___x_3453_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
lean_dec_ref(v_a_3428_);
return v___x_3485_;
}
else
{
lean_dec(v_a_3480_);
lean_dec_ref(v_body_3477_);
lean_dec(v_declName_3474_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
return v___x_3481_;
}
}
else
{
lean_dec_ref(v_body_3477_);
lean_dec_ref(v_value_3476_);
lean_dec(v_declName_3474_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
return v___x_3479_;
}
}
case 10:
{
lean_object* v_data_3486_; lean_object* v_expr_3487_; lean_object* v___x_3488_; 
lean_dec(v_a_3445_);
v_data_3486_ = lean_ctor_get(v_e_3424_, 0);
lean_inc(v_data_3486_);
v_expr_3487_ = lean_ctor_get(v_e_3424_, 1);
lean_inc_ref(v_expr_3487_);
v___x_3488_ = l_Lean_getRecAppSyntax_x3f(v_e_3424_);
lean_dec_ref_known(v_e_3424_, 2);
if (lean_obj_tag(v___x_3488_) == 1)
{
lean_object* v_val_3489_; lean_object* v_fileName_3490_; lean_object* v_fileMap_3491_; lean_object* v_options_3492_; lean_object* v_currRecDepth_3493_; lean_object* v_maxRecDepth_3494_; lean_object* v_ref_3495_; lean_object* v_currNamespace_3496_; lean_object* v_openDecls_3497_; lean_object* v_initHeartbeats_3498_; lean_object* v_maxHeartbeats_3499_; lean_object* v_quotContext_3500_; lean_object* v_currMacroScope_3501_; uint8_t v_diag_3502_; lean_object* v_cancelTk_x3f_3503_; uint8_t v_suppressElabErrors_3504_; lean_object* v_inheritedTraceOptions_3505_; lean_object* v_ref_3506_; lean_object* v___x_3507_; 
lean_dec(v_data_3486_);
v_val_3489_ = lean_ctor_get(v___x_3488_, 0);
lean_inc(v_val_3489_);
lean_dec_ref_known(v___x_3488_, 1);
v_fileName_3490_ = lean_ctor_get(v_a_3428_, 0);
lean_inc_ref(v_fileName_3490_);
v_fileMap_3491_ = lean_ctor_get(v_a_3428_, 1);
lean_inc_ref(v_fileMap_3491_);
v_options_3492_ = lean_ctor_get(v_a_3428_, 2);
lean_inc_ref(v_options_3492_);
v_currRecDepth_3493_ = lean_ctor_get(v_a_3428_, 3);
lean_inc(v_currRecDepth_3493_);
v_maxRecDepth_3494_ = lean_ctor_get(v_a_3428_, 4);
lean_inc(v_maxRecDepth_3494_);
v_ref_3495_ = lean_ctor_get(v_a_3428_, 5);
lean_inc(v_ref_3495_);
v_currNamespace_3496_ = lean_ctor_get(v_a_3428_, 6);
lean_inc(v_currNamespace_3496_);
v_openDecls_3497_ = lean_ctor_get(v_a_3428_, 7);
lean_inc(v_openDecls_3497_);
v_initHeartbeats_3498_ = lean_ctor_get(v_a_3428_, 8);
lean_inc(v_initHeartbeats_3498_);
v_maxHeartbeats_3499_ = lean_ctor_get(v_a_3428_, 9);
lean_inc(v_maxHeartbeats_3499_);
v_quotContext_3500_ = lean_ctor_get(v_a_3428_, 10);
lean_inc(v_quotContext_3500_);
v_currMacroScope_3501_ = lean_ctor_get(v_a_3428_, 11);
lean_inc(v_currMacroScope_3501_);
v_diag_3502_ = lean_ctor_get_uint8(v_a_3428_, sizeof(void*)*14);
v_cancelTk_x3f_3503_ = lean_ctor_get(v_a_3428_, 12);
lean_inc(v_cancelTk_x3f_3503_);
v_suppressElabErrors_3504_ = lean_ctor_get_uint8(v_a_3428_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3505_ = lean_ctor_get(v_a_3428_, 13);
lean_inc_ref(v_inheritedTraceOptions_3505_);
lean_dec_ref(v_a_3428_);
v_ref_3506_ = l_Lean_replaceRef(v_val_3489_, v_ref_3495_);
lean_dec(v_ref_3495_);
lean_dec(v_val_3489_);
v___x_3507_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3507_, 0, v_fileName_3490_);
lean_ctor_set(v___x_3507_, 1, v_fileMap_3491_);
lean_ctor_set(v___x_3507_, 2, v_options_3492_);
lean_ctor_set(v___x_3507_, 3, v_currRecDepth_3493_);
lean_ctor_set(v___x_3507_, 4, v_maxRecDepth_3494_);
lean_ctor_set(v___x_3507_, 5, v_ref_3506_);
lean_ctor_set(v___x_3507_, 6, v_currNamespace_3496_);
lean_ctor_set(v___x_3507_, 7, v_openDecls_3497_);
lean_ctor_set(v___x_3507_, 8, v_initHeartbeats_3498_);
lean_ctor_set(v___x_3507_, 9, v_maxHeartbeats_3499_);
lean_ctor_set(v___x_3507_, 10, v_quotContext_3500_);
lean_ctor_set(v___x_3507_, 11, v_currMacroScope_3501_);
lean_ctor_set(v___x_3507_, 12, v_cancelTk_x3f_3503_);
lean_ctor_set(v___x_3507_, 13, v_inheritedTraceOptions_3505_);
lean_ctor_set_uint8(v___x_3507_, sizeof(void*)*14, v_diag_3502_);
lean_ctor_set_uint8(v___x_3507_, sizeof(void*)*14 + 1, v_suppressElabErrors_3504_);
v_e_3424_ = v_expr_3487_;
v_a_3428_ = v___x_3507_;
goto _start;
}
else
{
lean_object* v___x_3509_; 
lean_dec(v___x_3488_);
v___x_3509_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v_below_3423_, v_expr_3487_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3518_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3512_ = v___x_3509_;
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3509_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3518_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3514_ = l_Lean_mkMData(v_data_3486_, v_a_3510_);
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3514_);
v___x_3516_ = v___x_3512_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3514_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
else
{
lean_dec(v_data_3486_);
return v___x_3509_;
}
}
}
case 11:
{
lean_object* v_typeName_3519_; lean_object* v_idx_3520_; lean_object* v_struct_3521_; lean_object* v___x_3522_; 
lean_dec(v_a_3445_);
v_typeName_3519_ = lean_ctor_get(v_e_3424_, 0);
lean_inc(v_typeName_3519_);
v_idx_3520_ = lean_ctor_get(v_e_3424_, 1);
lean_inc(v_idx_3520_);
v_struct_3521_ = lean_ctor_get(v_e_3424_, 2);
lean_inc_ref(v_struct_3521_);
lean_dec_ref_known(v_e_3424_, 3);
v___x_3522_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v_below_3423_, v_struct_3521_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3531_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3525_ = v___x_3522_;
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3522_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3531_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3529_; 
v___x_3527_ = l_Lean_mkProj(v_typeName_3519_, v_idx_3520_, v_a_3523_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set(v___x_3525_, 0, v___x_3527_);
v___x_3529_ = v___x_3525_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
else
{
lean_dec(v_idx_3520_);
lean_dec(v_typeName_3519_);
return v___x_3522_;
}
}
case 5:
{
uint8_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = lean_unbox(v_a_3445_);
lean_inc_ref(v_e_3424_);
v___x_3533_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3424_, v___x_3532_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
if (lean_obj_tag(v_a_3534_) == 0)
{
lean_dec(v_a_3445_);
v_e_3432_ = v_e_3424_;
v___y_3433_ = v_a_3425_;
v___y_3434_ = v_a_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
goto v___jp_3431_;
}
else
{
lean_object* v_val_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v_val_3535_ = lean_ctor_get(v_a_3534_, 0);
lean_inc(v_val_3535_);
lean_dec_ref_known(v_a_3534_, 1);
v___x_3536_ = lean_unsigned_to_nat(0u);
v___x_3537_ = lean_array_get_size(v_recArgInfos_3419_);
v___x_3538_ = lean_nat_dec_lt(v___x_3536_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_dec(v_val_3535_);
lean_dec(v_a_3445_);
v_e_3432_ = v_e_3424_;
v___y_3433_ = v_a_3425_;
v___y_3434_ = v_a_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
goto v___jp_3431_;
}
else
{
if (v___x_3538_ == 0)
{
lean_dec(v_val_3535_);
lean_dec(v_a_3445_);
v_e_3432_ = v_e_3424_;
v___y_3433_ = v_a_3425_;
v___y_3434_ = v_a_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
goto v___jp_3431_;
}
else
{
size_t v___x_3539_; size_t v___x_3540_; uint8_t v___x_3541_; 
v___x_3539_ = ((size_t)0ULL);
v___x_3540_ = lean_usize_of_nat(v___x_3537_);
v___x_3541_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3424_, v_recArgInfos_3419_, v___x_3539_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_dec(v_val_3535_);
lean_dec(v_a_3445_);
v_e_3432_ = v_e_3424_;
v___y_3433_ = v_a_3425_;
v___y_3434_ = v_a_3426_;
v___y_3435_ = v_a_3427_;
v___y_3436_ = v_a_3428_;
v___y_3437_ = v_a_3429_;
goto v___jp_3431_;
}
else
{
lean_object* v_inheritedTraceOptions_3542_; lean_object* v___x_3543_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___x_3613_; 
v_inheritedTraceOptions_3542_ = lean_ctor_get(v_a_3428_, 13);
v___x_3543_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3613_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3543_, v_inheritedTraceOptions_3542_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; uint8_t v___x_3615_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3615_ = lean_unbox(v_a_3614_);
lean_dec(v_a_3614_);
if (v___x_3615_ == 0)
{
v___y_3545_ = v_a_3425_;
v___y_3546_ = v_a_3426_;
v___y_3547_ = v_a_3427_;
v___y_3548_ = v_a_3428_;
v___y_3549_ = v_a_3429_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3616_; 
lean_inc(v_a_3429_);
lean_inc_ref(v_a_3428_);
lean_inc(v_a_3427_);
lean_inc_ref(v_a_3426_);
lean_inc_ref(v_below_3423_);
v___x_3616_ = lean_infer_type(v_below_3423_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3423_);
v___x_3619_ = l_Lean_MessageData_ofExpr(v_below_3423_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l_Lean_MessageData_ofExpr(v_a_3617_);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3543_, v___x_3624_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_dec_ref_known(v___x_3625_, 1);
v___y_3545_ = v_a_3425_;
v___y_3546_ = v_a_3426_;
v___y_3547_ = v_a_3427_;
v___y_3548_ = v_a_3428_;
v___y_3549_ = v_a_3429_;
goto v___jp_3544_;
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_val_3535_);
lean_dec_ref_known(v_e_3424_, 2);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_dec(v_val_3535_);
lean_dec_ref_known(v_e_3424_, 2);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
return v___x_3616_;
}
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_val_3535_);
lean_dec_ref_known(v_e_3424_, 2);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
v_a_3634_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3613_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3613_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
v___jp_3544_:
{
lean_object* v___x_3550_; 
lean_inc_ref(v_below_3423_);
v___x_3550_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3535_, v_below_3423_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3550_, 1);
if (lean_obj_tag(v_a_3551_) == 1)
{
lean_object* v_val_3552_; lean_object* v_toMatcherInfo_3553_; lean_object* v_matcherName_3554_; lean_object* v_matcherLevels_3555_; lean_object* v_params_3556_; lean_object* v_motive_3557_; lean_object* v_discrs_3558_; lean_object* v_alts_3559_; lean_object* v_remaining_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; lean_object* v___x_3564_; 
lean_dec_ref(v_below_3423_);
v_val_3552_ = lean_ctor_get(v_a_3551_, 0);
lean_inc(v_val_3552_);
lean_dec_ref_known(v_a_3551_, 1);
v_toMatcherInfo_3553_ = lean_ctor_get(v_val_3552_, 0);
lean_inc_ref(v_toMatcherInfo_3553_);
v_matcherName_3554_ = lean_ctor_get(v_val_3552_, 1);
lean_inc(v_matcherName_3554_);
v_matcherLevels_3555_ = lean_ctor_get(v_val_3552_, 2);
lean_inc_ref(v_matcherLevels_3555_);
v_params_3556_ = lean_ctor_get(v_val_3552_, 3);
lean_inc_ref(v_params_3556_);
v_motive_3557_ = lean_ctor_get(v_val_3552_, 4);
lean_inc_ref(v_motive_3557_);
v_discrs_3558_ = lean_ctor_get(v_val_3552_, 5);
lean_inc_ref(v_discrs_3558_);
v_alts_3559_ = lean_ctor_get(v_val_3552_, 6);
lean_inc_ref(v_alts_3559_);
v_remaining_3560_ = lean_ctor_get(v_val_3552_, 7);
lean_inc_ref(v_remaining_3560_);
v___x_3561_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3552_);
v___x_3562_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3563_ = lean_unbox(v_a_3445_);
lean_dec(v_a_3445_);
v___x_3564_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v___x_3563_, v_e_3424_, v_alts_3559_, v___x_3561_, v___x_3536_, v___x_3562_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v___x_3561_);
lean_dec_ref(v_alts_3559_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3574_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3567_ = v___x_3564_;
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3564_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3569_, 0, v_toMatcherInfo_3553_);
lean_ctor_set(v___x_3569_, 1, v_matcherName_3554_);
lean_ctor_set(v___x_3569_, 2, v_matcherLevels_3555_);
lean_ctor_set(v___x_3569_, 3, v_params_3556_);
lean_ctor_set(v___x_3569_, 4, v_motive_3557_);
lean_ctor_set(v___x_3569_, 5, v_discrs_3558_);
lean_ctor_set(v___x_3569_, 6, v_a_3565_);
lean_ctor_set(v___x_3569_, 7, v_remaining_3560_);
v___x_3570_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3569_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 0, v___x_3570_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref(v_remaining_3560_);
lean_dec_ref(v_discrs_3558_);
lean_dec_ref(v_motive_3557_);
lean_dec_ref(v_params_3556_);
lean_dec_ref(v_matcherLevels_3555_);
lean_dec(v_matcherName_3554_);
lean_dec_ref(v_toMatcherInfo_3553_);
v_a_3575_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3564_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3564_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_3583_; lean_object* v___x_3584_; 
lean_dec(v_a_3551_);
lean_dec(v_a_3445_);
v_inheritedTraceOptions_3583_ = lean_ctor_get(v___y_3548_, 13);
v___x_3584_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3543_, v_inheritedTraceOptions_3583_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; uint8_t v___x_3586_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
lean_dec_ref_known(v___x_3584_, 1);
v___x_3586_ = lean_unbox(v_a_3585_);
lean_dec(v_a_3585_);
if (v___x_3586_ == 0)
{
v_e_3432_ = v_e_3424_;
v___y_3433_ = v___y_3545_;
v___y_3434_ = v___y_3546_;
v___y_3435_ = v___y_3547_;
v___y_3436_ = v___y_3548_;
v___y_3437_ = v___y_3549_;
goto v___jp_3431_;
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3588_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3543_, v___x_3587_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_dec_ref_known(v___x_3588_, 1);
v_e_3432_ = v_e_3424_;
v___y_3433_ = v___y_3545_;
v___y_3434_ = v___y_3546_;
v___y_3435_ = v___y_3547_;
v___y_3436_ = v___y_3548_;
v___y_3437_ = v___y_3549_;
goto v___jp_3431_;
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v___y_3548_);
lean_dec_ref_known(v_e_3424_, 2);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3588_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3588_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v___y_3548_);
lean_dec_ref_known(v_e_3424_, 2);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
v_a_3597_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3584_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3584_);
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
}
}
else
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
lean_dec_ref(v___y_3548_);
lean_dec_ref_known(v_e_3424_, 2);
lean_dec(v_a_3445_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
v_a_3605_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3607_ = v___x_3550_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3550_);
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
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref_known(v_e_3424_, 2);
lean_dec(v_a_3445_);
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
v_a_3642_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3533_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3533_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
default: 
{
lean_object* v___x_3650_; 
lean_dec(v_a_3445_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
lean_inc_ref(v_e_3424_);
v___x_3650_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3421_, v_e_3424_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
lean_dec_ref(v_a_3428_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; 
v_unused_3658_ = lean_ctor_get(v___x_3650_, 0);
lean_dec(v_unused_3658_);
v___x_3652_ = v___x_3650_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_dec(v___x_3650_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_e_3424_);
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_e_3424_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
lean_dec_ref(v_e_3424_);
v_a_3659_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3650_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3650_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
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
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec_ref(v_a_3428_);
lean_dec_ref(v_e_3424_);
lean_dec_ref(v_below_3423_);
lean_dec_ref(v_containsRecFn_3422_);
lean_dec_ref(v_recFnNames_3421_);
lean_dec_ref(v_positions_3420_);
lean_dec_ref(v_recArgInfos_3419_);
v_a_3668_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3444_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3444_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
v___jp_3431_:
{
lean_object* v_dummy_3438_; lean_object* v_nargs_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_dummy_3438_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3439_ = l_Lean_Expr_getAppNumArgs(v_e_3432_);
lean_inc(v_nargs_3439_);
v___x_3440_ = lean_mk_array(v_nargs_3439_, v_dummy_3438_);
v___x_3441_ = lean_unsigned_to_nat(1u);
v___x_3442_ = lean_nat_sub(v_nargs_3439_, v___x_3441_);
lean_dec(v_nargs_3439_);
lean_inc_ref(v_e_3432_);
v___x_3443_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3419_, v_positions_3420_, v_recFnNames_3421_, v_containsRecFn_3422_, v_below_3423_, v_e_3432_, v_e_3432_, v___x_3440_, v___x_3442_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec_ref(v___y_3436_);
return v___x_3443_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3676_, lean_object* v_recArgInfos_3677_, lean_object* v_positions_3678_, lean_object* v_recFnNames_3679_, lean_object* v_containsRecFn_3680_, lean_object* v_below_3681_, lean_object* v_x_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_expr_instantiate1(v_body_3676_, v_x_3682_);
lean_inc_ref(v___y_3686_);
v___x_3690_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3677_, v_positions_3678_, v_recFnNames_3679_, v_containsRecFn_3680_, v_below_3681_, v___x_3689_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3691_, lean_object* v_positions_3692_, lean_object* v_recFnNames_3693_, lean_object* v_containsRecFn_3694_, lean_object* v_below_3695_, lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_bs_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
size_t v_sz_boxed_3705_; size_t v_i_boxed_3706_; lean_object* v_res_3707_; 
v_sz_boxed_3705_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3706_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3691_, v_positions_3692_, v_recFnNames_3693_, v_containsRecFn_3694_, v_below_3695_, v_sz_boxed_3705_, v_i_boxed_3706_, v_bs_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3708_, lean_object* v_positions_3709_, lean_object* v_recFnNames_3710_, lean_object* v_containsRecFn_3711_, lean_object* v_a_3712_, lean_object* v_e_3713_, lean_object* v_as_3714_, lean_object* v_bs_3715_, lean_object* v_i_3716_, lean_object* v_cs_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
uint8_t v_a_32864__boxed_3724_; lean_object* v_res_3725_; 
v_a_32864__boxed_3724_ = lean_unbox(v_a_3712_);
v_res_3725_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3708_, v_positions_3709_, v_recFnNames_3710_, v_containsRecFn_3711_, v_a_32864__boxed_3724_, v_e_3713_, v_as_3714_, v_bs_3715_, v_i_3716_, v_cs_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v_bs_3715_);
lean_dec_ref(v_as_3714_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3726_, lean_object* v_positions_3727_, lean_object* v_recFnNames_3728_, lean_object* v_containsRecFn_3729_, lean_object* v_below_3730_, lean_object* v_e_3731_, lean_object* v_x_3732_, lean_object* v_x_3733_, lean_object* v_x_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3726_, v_positions_3727_, v_recFnNames_3728_, v_containsRecFn_3729_, v_below_3730_, v_e_3731_, v_x_3732_, v_x_3733_, v_x_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3742_, lean_object* v_positions_3743_, lean_object* v_recFnNames_3744_, lean_object* v_containsRecFn_3745_, lean_object* v_below_3746_, lean_object* v_e_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3742_, v_positions_3743_, v_recFnNames_3744_, v_containsRecFn_3745_, v_below_3746_, v_e_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
lean_dec(v_a_3752_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
lean_dec(v_a_3748_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3755_, lean_object* v_msg_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; 
v___x_3763_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3756_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3764_, lean_object* v_msg_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3764_, v_msg_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v___y_3766_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3773_, lean_object* v_name_3774_, lean_object* v_type_3775_, lean_object* v_val_3776_, lean_object* v_k_3777_, uint8_t v_nondep_3778_, uint8_t v_kind_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3774_, v_type_3775_, v_val_3776_, v_k_3777_, v_nondep_3778_, v_kind_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3787_, lean_object* v_name_3788_, lean_object* v_type_3789_, lean_object* v_val_3790_, lean_object* v_k_3791_, lean_object* v_nondep_3792_, lean_object* v_kind_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
uint8_t v_nondep_boxed_3800_; uint8_t v_kind_boxed_3801_; lean_object* v_res_3802_; 
v_nondep_boxed_3800_ = lean_unbox(v_nondep_3792_);
v_kind_boxed_3801_ = lean_unbox(v_kind_3793_);
v_res_3802_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3787_, v_name_3788_, v_type_3789_, v_val_3790_, v_k_3791_, v_nondep_boxed_3800_, v_kind_boxed_3801_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3803_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3819_, lean_object* v_msg_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v___x_3827_; 
v___x_3827_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3819_, v_msg_3820_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3828_, lean_object* v_msg_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3828_, v_msg_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3837_, lean_object* v_constName_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3846_, lean_object* v_constName_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3846_, v_constName_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3855_, lean_object* v_ref_3856_, lean_object* v_constName_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3856_, v_constName_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3865_, lean_object* v_ref_3866_, lean_object* v_constName_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v_res_3874_; 
v_res_3874_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3865_, v_ref_3866_, v_constName_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec(v_ref_3866_);
return v_res_3874_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3875_, lean_object* v_ref_3876_, lean_object* v_msg_3877_, lean_object* v_declHint_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3876_, v_msg_3877_, v_declHint_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3886_, lean_object* v_ref_3887_, lean_object* v_msg_3888_, lean_object* v_declHint_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3886_, v_ref_3887_, v_msg_3888_, v_declHint_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v_ref_3887_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3897_, lean_object* v_declHint_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3897_, v_declHint_3898_, v___y_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3906_, lean_object* v_declHint_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3906_, v_declHint_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3915_, lean_object* v_ref_3916_, lean_object* v_msg_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v___x_3924_; 
v___x_3924_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3916_, v_msg_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3925_, lean_object* v_ref_3926_, lean_object* v_msg_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3925_, v_ref_3926_, v_msg_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec(v___y_3928_);
lean_dec(v_ref_3926_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3935_, lean_object* v_e_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v_fst_3945_; lean_object* v_snd_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3943_ = lean_st_ref_take(v___y_3937_);
v___x_3944_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3935_, v_e_3936_, v___x_3943_);
v_fst_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_fst_3945_);
v_snd_3946_ = lean_ctor_get(v___x_3944_, 1);
lean_inc(v_snd_3946_);
lean_dec_ref(v___x_3944_);
v___x_3947_ = lean_st_ref_set(v___y_3937_, v_snd_3946_);
v___x_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3948_, 0, v_fst_3945_);
return v___x_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3949_, lean_object* v_e_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3949_, v_e_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v_recFnNames_3949_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3958_, size_t v_i_3959_, lean_object* v_bs_3960_){
_start:
{
uint8_t v___x_3961_; 
v___x_3961_ = lean_usize_dec_lt(v_i_3959_, v_sz_3958_);
if (v___x_3961_ == 0)
{
return v_bs_3960_;
}
else
{
lean_object* v_v_3962_; lean_object* v_fnName_3963_; lean_object* v___x_3964_; lean_object* v_bs_x27_3965_; size_t v___x_3966_; size_t v___x_3967_; lean_object* v___x_3968_; 
v_v_3962_ = lean_array_uget_borrowed(v_bs_3960_, v_i_3959_);
v_fnName_3963_ = lean_ctor_get(v_v_3962_, 0);
lean_inc(v_fnName_3963_);
v___x_3964_ = lean_unsigned_to_nat(0u);
v_bs_x27_3965_ = lean_array_uset(v_bs_3960_, v_i_3959_, v___x_3964_);
v___x_3966_ = ((size_t)1ULL);
v___x_3967_ = lean_usize_add(v_i_3959_, v___x_3966_);
v___x_3968_ = lean_array_uset(v_bs_x27_3965_, v_i_3959_, v_fnName_3963_);
v_i_3959_ = v___x_3967_;
v_bs_3960_ = v___x_3968_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3970_, lean_object* v_i_3971_, lean_object* v_bs_3972_){
_start:
{
size_t v_sz_boxed_3973_; size_t v_i_boxed_3974_; lean_object* v_res_3975_; 
v_sz_boxed_3973_ = lean_unbox_usize(v_sz_3970_);
lean_dec(v_sz_3970_);
v_i_boxed_3974_ = lean_unbox_usize(v_i_3971_);
lean_dec(v_i_3971_);
v_res_3975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3973_, v_i_boxed_3974_, v_bs_3972_);
return v_res_3975_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = lean_box(0);
v___x_3977_ = lean_unsigned_to_nat(16u);
v___x_3978_ = lean_mk_array(v___x_3977_, v___x_3976_);
return v___x_3978_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3980_ = lean_unsigned_to_nat(0u);
v___x_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3980_);
lean_ctor_set(v___x_3981_, 1, v___x_3979_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3982_, lean_object* v_positions_3983_, lean_object* v_below_3984_, lean_object* v_e_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; size_t v_sz_3993_; size_t v___x_3994_; lean_object* v_recFnNames_3995_; lean_object* v_containsRecFn_3996_; lean_object* v___x_3997_; 
v___x_3991_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3992_ = lean_st_mk_ref(v___x_3991_);
v_sz_3993_ = lean_array_size(v_recArgInfos_3982_);
v___x_3994_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3982_);
v_recFnNames_3995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3993_, v___x_3994_, v_recArgInfos_3982_);
lean_inc_ref(v_recFnNames_3995_);
v_containsRecFn_3996_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3996_, 0, v_recFnNames_3995_);
lean_inc_ref(v_a_3988_);
v___x_3997_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3982_, v_positions_3983_, v_recFnNames_3995_, v_containsRecFn_3996_, v_below_3984_, v_e_3985_, v___x_3992_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___x_4000_; uint8_t v_isShared_4001_; uint8_t v_isSharedCheck_4006_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4000_ = v___x_3997_;
v_isShared_4001_ = v_isSharedCheck_4006_;
goto v_resetjp_3999_;
}
else
{
lean_inc(v_a_3998_);
lean_dec(v___x_3997_);
v___x_4000_ = lean_box(0);
v_isShared_4001_ = v_isSharedCheck_4006_;
goto v_resetjp_3999_;
}
v_resetjp_3999_:
{
lean_object* v___x_4002_; lean_object* v___x_4004_; 
v___x_4002_ = lean_st_ref_get(v___x_3992_);
lean_dec(v___x_3992_);
lean_dec(v___x_4002_);
if (v_isShared_4001_ == 0)
{
v___x_4004_ = v___x_4000_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3998_);
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
lean_dec(v___x_3992_);
return v___x_3997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_4007_, lean_object* v_positions_4008_, lean_object* v_below_4009_, lean_object* v_e_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4007_, v_positions_4008_, v_below_4009_, v_e_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4017_, lean_object* v_k_4018_, uint8_t v_cleanupAnnotations_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___f_4025_; uint8_t v___x_4026_; uint8_t v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___f_4025_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4025_, 0, v_k_4018_);
v___x_4026_ = 1;
v___x_4027_ = 0;
v___x_4028_ = lean_box(0);
v___x_4029_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4017_, v___x_4026_, v___x_4027_, v___x_4026_, v___x_4027_, v___x_4028_, v___f_4025_, v_cleanupAnnotations_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
v_a_4038_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4029_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4029_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4046_, lean_object* v_k_4047_, lean_object* v_cleanupAnnotations_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4054_; lean_object* v_res_4055_; 
v_cleanupAnnotations_boxed_4054_ = lean_unbox(v_cleanupAnnotations_4048_);
v_res_4055_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4046_, v_k_4047_, v_cleanupAnnotations_boxed_4054_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4056_, lean_object* v_e_4057_, lean_object* v_k_4058_, uint8_t v_cleanupAnnotations_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4057_, v_k_4058_, v_cleanupAnnotations_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4066_, lean_object* v_e_4067_, lean_object* v_k_4068_, lean_object* v_cleanupAnnotations_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4075_; lean_object* v_res_4076_; 
v_cleanupAnnotations_boxed_4075_ = lean_unbox(v_cleanupAnnotations_4069_);
v_res_4076_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4066_, v_e_4067_, v_k_4068_, v_cleanupAnnotations_boxed_4075_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4077_, lean_object* v_recArgInfo_4078_, lean_object* v_xs_4079_, lean_object* v___value_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v___x_4086_; 
v___x_4086_ = l_Lean_Meta_instantiateForall(v_type_4077_, v_xs_4079_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; lean_object* v_fst_4089_; lean_object* v_snd_4090_; uint8_t v___x_4091_; uint8_t v___x_4092_; uint8_t v___x_4093_; lean_object* v___x_4094_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___x_4086_, 1);
v___x_4088_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4078_, v_xs_4079_);
v_fst_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_fst_4089_);
v_snd_4090_ = lean_ctor_get(v___x_4088_, 1);
lean_inc(v_snd_4090_);
lean_dec_ref(v___x_4088_);
v___x_4091_ = 0;
v___x_4092_ = 1;
v___x_4093_ = 1;
v___x_4094_ = l_Lean_Meta_mkForallFVars(v_snd_4090_, v_a_4087_, v___x_4091_, v___x_4092_, v___x_4092_, v___x_4093_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v_snd_4090_);
if (lean_obj_tag(v___x_4094_) == 0)
{
lean_object* v_a_4095_; lean_object* v___x_4096_; 
v_a_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc(v_a_4095_);
lean_dec_ref_known(v___x_4094_, 1);
v___x_4096_ = l_Lean_Meta_mkLambdaFVars(v_fst_4089_, v_a_4095_, v___x_4091_, v___x_4092_, v___x_4091_, v___x_4092_, v___x_4093_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v_fst_4089_);
return v___x_4096_;
}
else
{
lean_dec(v_fst_4089_);
return v___x_4094_;
}
}
else
{
lean_dec_ref(v_xs_4079_);
lean_dec_ref(v_recArgInfo_4078_);
return v___x_4086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4097_, lean_object* v_recArgInfo_4098_, lean_object* v_xs_4099_, lean_object* v___value_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4097_, v_recArgInfo_4098_, v_xs_4099_, v___value_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec_ref(v___value_4100_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4107_, lean_object* v_value_4108_, lean_object* v_type_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_){
_start:
{
lean_object* v___f_4115_; uint8_t v___x_4116_; lean_object* v___x_4117_; 
v___f_4115_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4115_, 0, v_type_4109_);
lean_closure_set(v___f_4115_, 1, v_recArgInfo_4107_);
v___x_4116_ = 0;
v___x_4117_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4108_, v___f_4115_, v___x_4116_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4118_, lean_object* v_value_4119_, lean_object* v_type_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4118_, v_value_4119_, v_type_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4127_, lean_object* v_maxFVars_x3f_4128_, lean_object* v_k_4129_, uint8_t v_cleanupAnnotations_4130_, uint8_t v_whnfType_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___f_4137_; lean_object* v___x_4138_; 
v___f_4137_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4137_, 0, v_k_4129_);
v___x_4138_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4127_, v_maxFVars_x3f_4128_, v___f_4137_, v_cleanupAnnotations_4130_, v_whnfType_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
v_a_4147_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4138_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4138_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4155_, lean_object* v_maxFVars_x3f_4156_, lean_object* v_k_4157_, lean_object* v_cleanupAnnotations_4158_, lean_object* v_whnfType_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4165_; uint8_t v_whnfType_boxed_4166_; lean_object* v_res_4167_; 
v_cleanupAnnotations_boxed_4165_ = lean_unbox(v_cleanupAnnotations_4158_);
v_whnfType_boxed_4166_ = lean_unbox(v_whnfType_4159_);
v_res_4167_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4155_, v_maxFVars_x3f_4156_, v_k_4157_, v_cleanupAnnotations_boxed_4165_, v_whnfType_boxed_4166_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4168_, lean_object* v_type_4169_, lean_object* v_maxFVars_x3f_4170_, lean_object* v_k_4171_, uint8_t v_cleanupAnnotations_4172_, uint8_t v_whnfType_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4169_, v_maxFVars_x3f_4170_, v_k_4171_, v_cleanupAnnotations_4172_, v_whnfType_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4180_, lean_object* v_type_4181_, lean_object* v_maxFVars_x3f_4182_, lean_object* v_k_4183_, lean_object* v_cleanupAnnotations_4184_, lean_object* v_whnfType_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4191_; uint8_t v_whnfType_boxed_4192_; lean_object* v_res_4193_; 
v_cleanupAnnotations_boxed_4191_ = lean_unbox(v_cleanupAnnotations_4184_);
v_whnfType_boxed_4192_ = lean_unbox(v_whnfType_4185_);
v_res_4193_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4180_, v_type_4181_, v_maxFVars_x3f_4182_, v_k_4183_, v_cleanupAnnotations_boxed_4191_, v_whnfType_boxed_4192_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v_res_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4194_, lean_object* v_recArgInfos_4195_, lean_object* v_positions_4196_, lean_object* v_value_4197_, lean_object* v_fst_4198_, lean_object* v_snd_4199_, lean_object* v_below_4200_, lean_object* v_x_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4207_ = lean_unsigned_to_nat(0u);
v___x_4208_ = lean_array_get_borrowed(v___x_4194_, v_below_4200_, v___x_4207_);
lean_inc(v___x_4208_);
v___x_4209_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4195_, v_positions_4196_, v___x_4208_, v_value_4197_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; uint8_t v___x_4216_; uint8_t v___x_4217_; uint8_t v___x_4218_; lean_object* v___x_4219_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v___x_4211_ = lean_unsigned_to_nat(1u);
v___x_4212_ = lean_mk_empty_array_with_capacity(v___x_4211_);
lean_inc(v___x_4208_);
v___x_4213_ = lean_array_push(v___x_4212_, v___x_4208_);
v___x_4214_ = l_Array_append___redArg(v_fst_4198_, v___x_4213_);
lean_dec_ref(v___x_4213_);
v___x_4215_ = l_Array_append___redArg(v___x_4214_, v_snd_4199_);
v___x_4216_ = 0;
v___x_4217_ = 1;
v___x_4218_ = 1;
v___x_4219_ = l_Lean_Meta_mkLambdaFVars(v___x_4215_, v_a_4210_, v___x_4216_, v___x_4217_, v___x_4216_, v___x_4217_, v___x_4218_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec_ref(v___x_4215_);
return v___x_4219_;
}
else
{
lean_dec_ref(v_fst_4198_);
return v___x_4209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4220_, lean_object* v_recArgInfos_4221_, lean_object* v_positions_4222_, lean_object* v_value_4223_, lean_object* v_fst_4224_, lean_object* v_snd_4225_, lean_object* v_below_4226_, lean_object* v_x_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v_res_4233_; 
v_res_4233_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4220_, v_recArgInfos_4221_, v_positions_4222_, v_value_4223_, v_fst_4224_, v_snd_4225_, v_below_4226_, v_x_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec_ref(v_x_4227_);
lean_dec_ref(v_below_4226_);
lean_dec_ref(v_snd_4225_);
lean_dec_ref(v___x_4220_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4236_, lean_object* v_FType_4237_, lean_object* v___x_4238_, lean_object* v_recArgInfos_4239_, lean_object* v_positions_4240_, lean_object* v_xs_4241_, lean_object* v_value_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v___x_4248_; lean_object* v_fst_4249_; lean_object* v_snd_4250_; lean_object* v___x_4251_; 
v___x_4248_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4236_, v_xs_4241_);
v_fst_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_fst_4249_);
v_snd_4250_ = lean_ctor_get(v___x_4248_, 1);
lean_inc(v_snd_4250_);
lean_dec_ref(v___x_4248_);
v___x_4251_ = l_Lean_Meta_instantiateForall(v_FType_4237_, v_fst_4249_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; lean_object* v___f_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; lean_object* v___x_4256_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___x_4251_, 1);
v___f_4253_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4253_, 0, v___x_4238_);
lean_closure_set(v___f_4253_, 1, v_recArgInfos_4239_);
lean_closure_set(v___f_4253_, 2, v_positions_4240_);
lean_closure_set(v___f_4253_, 3, v_value_4242_);
lean_closure_set(v___f_4253_, 4, v_fst_4249_);
lean_closure_set(v___f_4253_, 5, v_snd_4250_);
v___x_4254_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4255_ = 0;
v___x_4256_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4252_, v___x_4254_, v___f_4253_, v___x_4255_, v___x_4255_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
return v___x_4256_;
}
else
{
lean_dec(v_snd_4250_);
lean_dec(v_fst_4249_);
lean_dec_ref(v_value_4242_);
lean_dec_ref(v_positions_4240_);
lean_dec_ref(v_recArgInfos_4239_);
lean_dec_ref(v___x_4238_);
return v___x_4251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4257_, lean_object* v_FType_4258_, lean_object* v___x_4259_, lean_object* v_recArgInfos_4260_, lean_object* v_positions_4261_, lean_object* v_xs_4262_, lean_object* v_value_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4257_, v_FType_4258_, v___x_4259_, v_recArgInfos_4260_, v_positions_4261_, v_xs_4262_, v_value_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4270_, lean_object* v_positions_4271_, lean_object* v_recArgInfo_4272_, lean_object* v_value_4273_, lean_object* v_FType_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v___x_4280_; lean_object* v___f_4281_; uint8_t v___x_4282_; lean_object* v___x_4283_; 
v___x_4280_ = l_Lean_instInhabitedExpr;
v___f_4281_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4281_, 0, v_recArgInfo_4272_);
lean_closure_set(v___f_4281_, 1, v_FType_4274_);
lean_closure_set(v___f_4281_, 2, v___x_4280_);
lean_closure_set(v___f_4281_, 3, v_recArgInfos_4270_);
lean_closure_set(v___f_4281_, 4, v_positions_4271_);
v___x_4282_ = 0;
v___x_4283_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4273_, v___f_4281_, v___x_4282_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4284_, lean_object* v_positions_4285_, lean_object* v_recArgInfo_4286_, lean_object* v_value_4287_, lean_object* v_FType_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4284_, v_positions_4285_, v_recArgInfo_4286_, v_value_4287_, v_FType_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4295_, lean_object* v_params_4296_, uint8_t v_isIndPred_4297_, lean_object* v_brecOnUniv_4298_, lean_object* v_levels_4299_, lean_object* v_idx_4300_){
_start:
{
lean_object* v_n_4301_; lean_object* v___y_4303_; 
v_n_4301_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4295_, v_idx_4300_);
if (v_isIndPred_4297_ == 0)
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4306_, 0, v_brecOnUniv_4298_);
lean_ctor_set(v___x_4306_, 1, v_levels_4299_);
v___y_4303_ = v___x_4306_;
goto v___jp_4302_;
}
else
{
lean_dec(v_brecOnUniv_4298_);
v___y_4303_ = v_levels_4299_;
goto v___jp_4302_;
}
v___jp_4302_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = l_Lean_Expr_const___override(v_n_4301_, v___y_4303_);
v___x_4305_ = l_Lean_mkAppN(v___x_4304_, v_params_4296_);
return v___x_4305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4307_, lean_object* v_params_4308_, lean_object* v_isIndPred_4309_, lean_object* v_brecOnUniv_4310_, lean_object* v_levels_4311_, lean_object* v_idx_4312_){
_start:
{
uint8_t v_isIndPred_boxed_4313_; lean_object* v_res_4314_; 
v_isIndPred_boxed_4313_ = lean_unbox(v_isIndPred_4309_);
v_res_4314_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4307_, v_params_4308_, v_isIndPred_boxed_4313_, v_brecOnUniv_4310_, v_levels_4311_, v_idx_4312_);
lean_dec(v_idx_4312_);
lean_dec_ref(v_params_4308_);
lean_dec_ref(v_toIndGroupInfo_4307_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4315_, lean_object* v_a_4316_, lean_object* v_n_4317_){
_start:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4318_ = lean_apply_1(v_brecOnCons_4315_, v_n_4317_);
v___x_4319_ = l_Lean_mkAppN(v___x_4318_, v_a_4316_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4320_, lean_object* v_a_4321_, lean_object* v_n_4322_){
_start:
{
lean_object* v_res_4323_; 
v_res_4323_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4320_, v_a_4321_, v_n_4322_);
lean_dec_ref(v_a_4321_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4324_, lean_object* v_type_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_Meta_getLevel(v_type_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
return v___x_4331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4332_, lean_object* v_type_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4332_, v_type_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec_ref(v_x_4332_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4340_, size_t v_sz_4341_, size_t v_i_4342_, lean_object* v_bs_4343_){
_start:
{
uint8_t v___x_4344_; 
v___x_4344_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
if (v___x_4344_ == 0)
{
return v_bs_4343_;
}
else
{
lean_object* v___x_4345_; lean_object* v_v_4346_; lean_object* v___x_4347_; lean_object* v_bs_x27_4348_; lean_object* v___x_4349_; size_t v___x_4350_; size_t v___x_4351_; lean_object* v___x_4352_; 
v___x_4345_ = l_Lean_instInhabitedExpr;
v_v_4346_ = lean_array_uget(v_bs_4343_, v_i_4342_);
v___x_4347_ = lean_unsigned_to_nat(0u);
v_bs_x27_4348_ = lean_array_uset(v_bs_4343_, v_i_4342_, v___x_4347_);
v___x_4349_ = lean_array_get_borrowed(v___x_4345_, v_xs_4340_, v_v_4346_);
lean_dec(v_v_4346_);
v___x_4350_ = ((size_t)1ULL);
v___x_4351_ = lean_usize_add(v_i_4342_, v___x_4350_);
lean_inc(v___x_4349_);
v___x_4352_ = lean_array_uset(v_bs_x27_4348_, v_i_4342_, v___x_4349_);
v_i_4342_ = v___x_4351_;
v_bs_4343_ = v___x_4352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4354_, lean_object* v_sz_4355_, lean_object* v_i_4356_, lean_object* v_bs_4357_){
_start:
{
size_t v_sz_boxed_4358_; size_t v_i_boxed_4359_; lean_object* v_res_4360_; 
v_sz_boxed_4358_ = lean_unbox_usize(v_sz_4355_);
lean_dec(v_sz_4355_);
v_i_boxed_4359_ = lean_unbox_usize(v_i_4356_);
lean_dec(v_i_4356_);
v_res_4360_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4354_, v_sz_boxed_4358_, v_i_boxed_4359_, v_bs_4357_);
lean_dec_ref(v_xs_4354_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4361_, lean_object* v_f_4362_, lean_object* v_as_4363_, lean_object* v_bs_4364_, lean_object* v_i_4365_, lean_object* v_cs_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; uint8_t v___x_4373_; 
v___x_4372_ = lean_array_get_size(v_as_4363_);
v___x_4373_ = lean_nat_dec_lt(v_i_4365_, v___x_4372_);
if (v___x_4373_ == 0)
{
lean_object* v___x_4374_; 
lean_dec(v_i_4365_);
lean_dec_ref(v_f_4362_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_cs_4366_);
return v___x_4374_;
}
else
{
lean_object* v___x_4375_; uint8_t v___x_4376_; 
v___x_4375_ = lean_array_get_size(v_bs_4364_);
v___x_4376_ = lean_nat_dec_lt(v_i_4365_, v___x_4375_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; 
lean_dec(v_i_4365_);
lean_dec_ref(v_f_4362_);
v___x_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4377_, 0, v_cs_4366_);
return v___x_4377_;
}
else
{
lean_object* v_a_4378_; lean_object* v_b_4379_; size_t v_sz_4380_; size_t v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_a_4378_ = lean_array_fget_borrowed(v_as_4363_, v_i_4365_);
v_b_4379_ = lean_array_fget_borrowed(v_bs_4364_, v_i_4365_);
v_sz_4380_ = lean_array_size(v_b_4379_);
v___x_4381_ = ((size_t)0ULL);
lean_inc(v_b_4379_);
v___x_4382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4361_, v_sz_4380_, v___x_4381_, v_b_4379_);
lean_inc_ref(v_f_4362_);
lean_inc(v___y_4370_);
lean_inc_ref(v___y_4369_);
lean_inc(v___y_4368_);
lean_inc_ref(v___y_4367_);
lean_inc(v_a_4378_);
v___x_4383_ = lean_apply_7(v_f_4362_, v_a_4378_, v___x_4382_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, lean_box(0));
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v___x_4383_, 1);
v___x_4385_ = lean_unsigned_to_nat(1u);
v___x_4386_ = lean_nat_add(v_i_4365_, v___x_4385_);
lean_dec(v_i_4365_);
v___x_4387_ = lean_array_push(v_cs_4366_, v_a_4384_);
v_i_4365_ = v___x_4386_;
v_cs_4366_ = v___x_4387_;
goto _start;
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_dec_ref(v_cs_4366_);
lean_dec(v_i_4365_);
lean_dec_ref(v_f_4362_);
v_a_4389_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4383_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4383_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4397_, lean_object* v_f_4398_, lean_object* v_as_4399_, lean_object* v_bs_4400_, lean_object* v_i_4401_, lean_object* v_cs_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4397_, v_f_4398_, v_as_4399_, v_bs_4400_, v_i_4401_, v_cs_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec_ref(v_bs_4400_);
lean_dec_ref(v_as_4399_);
lean_dec_ref(v_xs_4397_);
return v_res_4408_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Array_instInhabited(lean_box(0));
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v___x_4416_; lean_object* v_toApplicative_4417_; lean_object* v_toFunctor_4418_; lean_object* v_toSeq_4419_; lean_object* v_toSeqLeft_4420_; lean_object* v_toSeqRight_4421_; lean_object* v___f_4422_; lean_object* v___f_4423_; lean_object* v___f_4424_; lean_object* v___f_4425_; lean_object* v___x_4426_; lean_object* v___f_4427_; lean_object* v___f_4428_; lean_object* v___f_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v_toApplicative_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4464_; 
v___x_4416_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4417_ = lean_ctor_get(v___x_4416_, 0);
v_toFunctor_4418_ = lean_ctor_get(v_toApplicative_4417_, 0);
v_toSeq_4419_ = lean_ctor_get(v_toApplicative_4417_, 2);
v_toSeqLeft_4420_ = lean_ctor_get(v_toApplicative_4417_, 3);
v_toSeqRight_4421_ = lean_ctor_get(v_toApplicative_4417_, 4);
v___f_4422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4423_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4418_, 2);
v___f_4424_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4424_, 0, v_toFunctor_4418_);
v___f_4425_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4425_, 0, v_toFunctor_4418_);
v___x_4426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4426_, 0, v___f_4424_);
lean_ctor_set(v___x_4426_, 1, v___f_4425_);
lean_inc(v_toSeqRight_4421_);
v___f_4427_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4427_, 0, v_toSeqRight_4421_);
lean_inc(v_toSeqLeft_4420_);
v___f_4428_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4428_, 0, v_toSeqLeft_4420_);
lean_inc(v_toSeq_4419_);
v___f_4429_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4429_, 0, v_toSeq_4419_);
v___x_4430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4426_);
lean_ctor_set(v___x_4430_, 1, v___f_4422_);
lean_ctor_set(v___x_4430_, 2, v___f_4429_);
lean_ctor_set(v___x_4430_, 3, v___f_4428_);
lean_ctor_set(v___x_4430_, 4, v___f_4427_);
v___x_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
lean_ctor_set(v___x_4431_, 1, v___f_4423_);
v___x_4432_ = l_StateRefT_x27_instMonad___redArg(v___x_4431_);
v_toApplicative_4433_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4464_ == 0)
{
lean_object* v_unused_4465_; 
v_unused_4465_ = lean_ctor_get(v___x_4432_, 1);
lean_dec(v_unused_4465_);
v___x_4435_ = v___x_4432_;
v_isShared_4436_ = v_isSharedCheck_4464_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_toApplicative_4433_);
lean_dec(v___x_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4464_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v_toFunctor_4437_; lean_object* v_toSeq_4438_; lean_object* v_toSeqLeft_4439_; lean_object* v_toSeqRight_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4462_; 
v_toFunctor_4437_ = lean_ctor_get(v_toApplicative_4433_, 0);
v_toSeq_4438_ = lean_ctor_get(v_toApplicative_4433_, 2);
v_toSeqLeft_4439_ = lean_ctor_get(v_toApplicative_4433_, 3);
v_toSeqRight_4440_ = lean_ctor_get(v_toApplicative_4433_, 4);
v_isSharedCheck_4462_ = !lean_is_exclusive(v_toApplicative_4433_);
if (v_isSharedCheck_4462_ == 0)
{
lean_object* v_unused_4463_; 
v_unused_4463_ = lean_ctor_get(v_toApplicative_4433_, 1);
lean_dec(v_unused_4463_);
v___x_4442_ = v_toApplicative_4433_;
v_isShared_4443_ = v_isSharedCheck_4462_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_toSeqRight_4440_);
lean_inc(v_toSeqLeft_4439_);
lean_inc(v_toSeq_4438_);
lean_inc(v_toFunctor_4437_);
lean_dec(v_toApplicative_4433_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4462_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___f_4446_; lean_object* v___f_4447_; lean_object* v___x_4448_; lean_object* v___f_4449_; lean_object* v___f_4450_; lean_object* v___f_4451_; lean_object* v___x_4453_; 
v___f_4444_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4445_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4437_);
v___f_4446_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4446_, 0, v_toFunctor_4437_);
v___f_4447_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4447_, 0, v_toFunctor_4437_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___f_4446_);
lean_ctor_set(v___x_4448_, 1, v___f_4447_);
v___f_4449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4449_, 0, v_toSeqRight_4440_);
v___f_4450_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4450_, 0, v_toSeqLeft_4439_);
v___f_4451_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4451_, 0, v_toSeq_4438_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set(v___x_4442_, 4, v___f_4449_);
lean_ctor_set(v___x_4442_, 3, v___f_4450_);
lean_ctor_set(v___x_4442_, 2, v___f_4451_);
lean_ctor_set(v___x_4442_, 1, v___f_4444_);
lean_ctor_set(v___x_4442_, 0, v___x_4448_);
v___x_4453_ = v___x_4442_;
goto v_reusejp_4452_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v___x_4448_);
lean_ctor_set(v_reuseFailAlloc_4461_, 1, v___f_4444_);
lean_ctor_set(v_reuseFailAlloc_4461_, 2, v___f_4451_);
lean_ctor_set(v_reuseFailAlloc_4461_, 3, v___f_4450_);
lean_ctor_set(v_reuseFailAlloc_4461_, 4, v___f_4449_);
v___x_4453_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4452_;
}
v_reusejp_4452_:
{
lean_object* v___x_4455_; 
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 1, v___f_4445_);
lean_ctor_set(v___x_4435_, 0, v___x_4453_);
v___x_4455_ = v___x_4435_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4453_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v___f_4445_);
v___x_4455_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_940__overap_4458_; lean_object* v___x_4459_; 
v___x_4456_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4457_ = l_instInhabitedOfMonad___redArg(v___x_4455_, v___x_4456_);
v___x_940__overap_4458_ = lean_panic_fn_borrowed(v___x_4457_, v_msg_4410_);
lean_dec(v___x_4457_);
lean_inc(v___y_4414_);
lean_inc_ref(v___y_4413_);
lean_inc(v___y_4412_);
lean_inc_ref(v___y_4411_);
v___x_4459_ = lean_apply_5(v___x_940__overap_4458_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, lean_box(0));
return v___x_4459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
return v_res_4472_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4476_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4477_ = lean_unsigned_to_nat(2u);
v___x_4478_ = lean_unsigned_to_nat(73u);
v___x_4479_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4480_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4481_ = l_mkPanicMessageWithDecl(v___x_4480_, v___x_4479_, v___x_4478_, v___x_4477_, v___x_4476_);
return v___x_4481_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4483_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4484_ = lean_unsigned_to_nat(2u);
v___x_4485_ = lean_unsigned_to_nat(74u);
v___x_4486_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4487_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4488_ = l_mkPanicMessageWithDecl(v___x_4487_, v___x_4486_, v___x_4485_, v___x_4484_, v___x_4483_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4491_, lean_object* v_positions_4492_, lean_object* v_ys_4493_, lean_object* v_xs_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; lean_object* v___x_4501_; uint8_t v___x_4502_; 
v___x_4500_ = lean_array_get_size(v_positions_4492_);
v___x_4501_ = lean_array_get_size(v_ys_4493_);
v___x_4502_ = lean_nat_dec_eq(v___x_4500_, v___x_4501_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; lean_object* v___x_4504_; 
lean_dec_ref(v_f_4491_);
v___x_4503_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4504_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4503_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4504_;
}
else
{
lean_object* v___x_4505_; lean_object* v___x_4506_; uint8_t v___x_4507_; 
v___x_4505_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4492_);
v___x_4506_ = lean_array_get_size(v_xs_4494_);
v___x_4507_ = lean_nat_dec_eq(v___x_4505_, v___x_4506_);
lean_dec(v___x_4505_);
if (v___x_4507_ == 0)
{
lean_object* v___x_4508_; lean_object* v___x_4509_; 
lean_dec_ref(v_f_4491_);
v___x_4508_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4509_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4508_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4509_;
}
else
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; 
v___x_4510_ = lean_unsigned_to_nat(0u);
v___x_4511_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4512_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4494_, v_f_4491_, v_ys_4493_, v_positions_4492_, v___x_4510_, v___x_4511_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4513_, lean_object* v_positions_4514_, lean_object* v_ys_4515_, lean_object* v_xs_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4513_, v_positions_4514_, v_ys_4515_, v_xs_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec_ref(v_xs_4516_);
lean_dec_ref(v_ys_4515_);
lean_dec_ref(v_positions_4514_);
return v_res_4522_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = lean_unsigned_to_nat(0u);
v___x_4525_ = l_Lean_Level_ofNat(v___x_4524_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4526_, lean_object* v_positions_4527_, lean_object* v_motives_4528_, uint8_t v_isIndPred_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v_indGroupInst_4538_; lean_object* v_brecOnUniv_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; 
v___x_4535_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4536_ = lean_unsigned_to_nat(0u);
v___x_4537_ = lean_array_get_borrowed(v___x_4535_, v_recArgInfos_4526_, v___x_4536_);
v_indGroupInst_4538_ = lean_ctor_get(v___x_4537_, 4);
if (v_isIndPred_4529_ == 0)
{
lean_object* v___f_4581_; lean_object* v___x_4582_; lean_object* v_motive_4583_; lean_object* v___x_4584_; 
v___f_4581_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4582_ = l_Lean_instInhabitedExpr;
v_motive_4583_ = lean_array_get_borrowed(v___x_4582_, v_motives_4528_, v___x_4536_);
lean_inc(v_motive_4583_);
v___x_4584_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4583_, v___f_4581_, v_isIndPred_4529_, v_a_4530_, v_a_4531_, v_a_4532_, v_a_4533_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref_known(v___x_4584_, 1);
v_brecOnUniv_4540_ = v_a_4585_;
v___y_4541_ = v_a_4530_;
v___y_4542_ = v_a_4531_;
v___y_4543_ = v_a_4532_;
v___y_4544_ = v_a_4533_;
goto v___jp_4539_;
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
v_a_4586_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4584_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4584_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
else
{
lean_object* v___x_4594_; 
v___x_4594_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4540_ = v___x_4594_;
v___y_4541_ = v_a_4530_;
v___y_4542_ = v_a_4531_;
v___y_4543_ = v_a_4532_;
v___y_4544_ = v_a_4533_;
goto v___jp_4539_;
}
v___jp_4539_:
{
lean_object* v_toIndGroupInfo_4545_; lean_object* v_levels_4546_; lean_object* v_params_4547_; lean_object* v___x_4548_; lean_object* v_brecOnCons_4549_; lean_object* v_brecOnAux_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v_toIndGroupInfo_4545_ = lean_ctor_get(v_indGroupInst_4538_, 0);
v_levels_4546_ = lean_ctor_get(v_indGroupInst_4538_, 1);
v_params_4547_ = lean_ctor_get(v_indGroupInst_4538_, 2);
v___x_4548_ = lean_box(v_isIndPred_4529_);
lean_inc_n(v_levels_4546_, 2);
lean_inc(v_brecOnUniv_4540_);
lean_inc_ref(v_params_4547_);
lean_inc_ref(v_toIndGroupInfo_4545_);
v_brecOnCons_4549_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4549_, 0, v_toIndGroupInfo_4545_);
lean_closure_set(v_brecOnCons_4549_, 1, v_params_4547_);
lean_closure_set(v_brecOnCons_4549_, 2, v___x_4548_);
lean_closure_set(v_brecOnCons_4549_, 3, v_brecOnUniv_4540_);
lean_closure_set(v_brecOnCons_4549_, 4, v_levels_4546_);
v_brecOnAux_4550_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4545_, v_params_4547_, v_isIndPred_4529_, v_brecOnUniv_4540_, v_levels_4546_, v___x_4536_);
v___x_4551_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4545_);
v___x_4552_ = l_Lean_Meta_inferArgumentTypesN(v___x_4551_, v_brecOnAux_4550_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
if (lean_obj_tag(v___x_4552_) == 0)
{
lean_object* v_a_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_a_4553_ = lean_ctor_get(v___x_4552_, 0);
lean_inc(v_a_4553_);
lean_dec_ref_known(v___x_4552_, 1);
v___x_4554_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4555_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4554_, v_positions_4527_, v_a_4553_, v_motives_4528_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v_a_4553_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4564_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4558_ = v___x_4555_;
v_isShared_4559_ = v_isSharedCheck_4564_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4555_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4564_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___f_4560_; lean_object* v___x_4562_; 
v___f_4560_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4560_, 0, v_brecOnCons_4549_);
lean_closure_set(v___f_4560_, 1, v_a_4556_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 0, v___f_4560_);
v___x_4562_ = v___x_4558_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___f_4560_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
else
{
lean_object* v_a_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4572_; 
lean_dec_ref(v_brecOnCons_4549_);
v_a_4565_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4572_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4572_ == 0)
{
v___x_4567_ = v___x_4555_;
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_a_4565_);
lean_dec(v___x_4555_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4572_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4570_; 
if (v_isShared_4568_ == 0)
{
v___x_4570_ = v___x_4567_;
goto v_reusejp_4569_;
}
else
{
lean_object* v_reuseFailAlloc_4571_; 
v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
v___x_4570_ = v_reuseFailAlloc_4571_;
goto v_reusejp_4569_;
}
v_reusejp_4569_:
{
return v___x_4570_;
}
}
}
}
else
{
lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4580_; 
lean_dec_ref(v_brecOnCons_4549_);
v_a_4573_ = lean_ctor_get(v___x_4552_, 0);
v_isSharedCheck_4580_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4580_ == 0)
{
v___x_4575_ = v___x_4552_;
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4552_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4580_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4573_);
v___x_4578_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
return v___x_4578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4595_, lean_object* v_positions_4596_, lean_object* v_motives_4597_, lean_object* v_isIndPred_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
uint8_t v_isIndPred_boxed_4604_; lean_object* v_res_4605_; 
v_isIndPred_boxed_4604_ = lean_unbox(v_isIndPred_4598_);
v_res_4605_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4595_, v_positions_4596_, v_motives_4597_, v_isIndPred_boxed_4604_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec_ref(v_motives_4597_);
lean_dec_ref(v_positions_4596_);
lean_dec_ref(v_recArgInfos_4595_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4606_, lean_object* v_msg_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
return v___x_4613_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4614_, lean_object* v_msg_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v_res_4621_; 
v_res_4621_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4614_, v_msg_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
return v_res_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4622_, lean_object* v_00_u03b1_4623_, lean_object* v_f_4624_, lean_object* v_positions_4625_, lean_object* v_ys_4626_, lean_object* v_xs_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_){
_start:
{
lean_object* v___x_4633_; 
v___x_4633_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4624_, v_positions_4625_, v_ys_4626_, v_xs_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4634_, lean_object* v_00_u03b1_4635_, lean_object* v_f_4636_, lean_object* v_positions_4637_, lean_object* v_ys_4638_, lean_object* v_xs_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4634_, v_00_u03b1_4635_, v_f_4636_, v_positions_4637_, v_ys_4638_, v_xs_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec_ref(v_xs_4639_);
lean_dec_ref(v_ys_4638_);
lean_dec_ref(v_positions_4637_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4646_, lean_object* v_00_u03b3_4647_, lean_object* v_xs_4648_, lean_object* v_f_4649_, lean_object* v_as_4650_, lean_object* v_bs_4651_, lean_object* v_i_4652_, lean_object* v_cs_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4648_, v_f_4649_, v_as_4650_, v_bs_4651_, v_i_4652_, v_cs_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4660_, lean_object* v_00_u03b3_4661_, lean_object* v_xs_4662_, lean_object* v_f_4663_, lean_object* v_as_4664_, lean_object* v_bs_4665_, lean_object* v_i_4666_, lean_object* v_cs_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4660_, v_00_u03b3_4661_, v_xs_4662_, v_f_4663_, v_as_4664_, v_bs_4665_, v_i_4666_, v_cs_4667_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec_ref(v_bs_4665_);
lean_dec_ref(v_as_4664_);
lean_dec_ref(v_xs_4662_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4674_, lean_object* v_e_4675_){
_start:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = l_Lean_indentD(v_e_4675_);
v___x_4677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4674_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
return v___x_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4678_, lean_object* v_x_4679_, lean_object* v_brecOnType_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
lean_object* v___x_4686_; 
v___x_4686_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4678_, v_brecOnType_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
return v___x_4686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4687_, lean_object* v_x_4688_, lean_object* v_brecOnType_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4687_, v_x_4688_, v_brecOnType_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec_ref(v_x_4688_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4696_, lean_object* v_as_4697_, size_t v_sz_4698_, size_t v_i_4699_, lean_object* v_b_4700_){
_start:
{
uint8_t v___x_4702_; 
v___x_4702_ = lean_usize_dec_lt(v_i_4699_, v_sz_4698_);
if (v___x_4702_ == 0)
{
lean_object* v___x_4703_; 
lean_dec_ref(v_a_4696_);
v___x_4703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4703_, 0, v_b_4700_);
return v___x_4703_;
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4705_; size_t v___x_4706_; size_t v___x_4707_; 
v_a_4704_ = lean_array_uget_borrowed(v_as_4697_, v_i_4699_);
lean_inc_ref(v_a_4696_);
v___x_4705_ = lean_array_set(v_b_4700_, v_a_4704_, v_a_4696_);
v___x_4706_ = ((size_t)1ULL);
v___x_4707_ = lean_usize_add(v_i_4699_, v___x_4706_);
v_i_4699_ = v___x_4707_;
v_b_4700_ = v___x_4705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4709_, lean_object* v_as_4710_, lean_object* v_sz_4711_, lean_object* v_i_4712_, lean_object* v_b_4713_, lean_object* v___y_4714_){
_start:
{
size_t v_sz_boxed_4715_; size_t v_i_boxed_4716_; lean_object* v_res_4717_; 
v_sz_boxed_4715_ = lean_unbox_usize(v_sz_4711_);
lean_dec(v_sz_4711_);
v_i_boxed_4716_ = lean_unbox_usize(v_i_4712_);
lean_dec(v_i_4712_);
v_res_4717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4709_, v_as_4710_, v_sz_boxed_4715_, v_i_boxed_4716_, v_b_4713_);
lean_dec_ref(v_as_4710_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4718_, size_t v_sz_4719_, size_t v_i_4720_, lean_object* v_b_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
uint8_t v___x_4727_; 
v___x_4727_ = lean_usize_dec_lt(v_i_4720_, v_sz_4719_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; 
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v_b_4721_);
return v___x_4728_;
}
else
{
lean_object* v_snd_4729_; lean_object* v_fst_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4774_; 
v_snd_4729_ = lean_ctor_get(v_b_4721_, 1);
v_fst_4730_ = lean_ctor_get(v_b_4721_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v_b_4721_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4732_ = v_b_4721_;
v_isShared_4733_ = v_isSharedCheck_4774_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_snd_4729_);
lean_inc(v_fst_4730_);
lean_dec(v_b_4721_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4774_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v_array_4734_; lean_object* v_start_4735_; lean_object* v_stop_4736_; uint8_t v___x_4737_; 
v_array_4734_ = lean_ctor_get(v_snd_4729_, 0);
v_start_4735_ = lean_ctor_get(v_snd_4729_, 1);
v_stop_4736_ = lean_ctor_get(v_snd_4729_, 2);
v___x_4737_ = lean_nat_dec_lt(v_start_4735_, v_stop_4736_);
if (v___x_4737_ == 0)
{
lean_object* v___x_4739_; 
if (v_isShared_4733_ == 0)
{
v___x_4739_ = v___x_4732_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_fst_4730_);
lean_ctor_set(v_reuseFailAlloc_4741_, 1, v_snd_4729_);
v___x_4739_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
lean_object* v___x_4740_; 
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
return v___x_4740_;
}
}
else
{
lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4770_; 
lean_inc(v_stop_4736_);
lean_inc(v_start_4735_);
lean_inc_ref(v_array_4734_);
v_isSharedCheck_4770_ = !lean_is_exclusive(v_snd_4729_);
if (v_isSharedCheck_4770_ == 0)
{
lean_object* v_unused_4771_; lean_object* v_unused_4772_; lean_object* v_unused_4773_; 
v_unused_4771_ = lean_ctor_get(v_snd_4729_, 2);
lean_dec(v_unused_4771_);
v_unused_4772_ = lean_ctor_get(v_snd_4729_, 1);
lean_dec(v_unused_4772_);
v_unused_4773_ = lean_ctor_get(v_snd_4729_, 0);
lean_dec(v_unused_4773_);
v___x_4743_ = v_snd_4729_;
v_isShared_4744_ = v_isSharedCheck_4770_;
goto v_resetjp_4742_;
}
else
{
lean_dec(v_snd_4729_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4770_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v_a_4745_; lean_object* v___x_4746_; size_t v_sz_4747_; size_t v___x_4748_; lean_object* v___x_4749_; 
v_a_4745_ = lean_array_uget_borrowed(v_as_4718_, v_i_4720_);
v___x_4746_ = lean_array_fget_borrowed(v_array_4734_, v_start_4735_);
v_sz_4747_ = lean_array_size(v___x_4746_);
v___x_4748_ = ((size_t)0ULL);
lean_inc(v_a_4745_);
v___x_4749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4745_, v___x_4746_, v_sz_4747_, v___x_4748_, v_fst_4730_);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v_a_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4754_; 
v_a_4750_ = lean_ctor_get(v___x_4749_, 0);
lean_inc(v_a_4750_);
lean_dec_ref_known(v___x_4749_, 1);
v___x_4751_ = lean_unsigned_to_nat(1u);
v___x_4752_ = lean_nat_add(v_start_4735_, v___x_4751_);
lean_dec(v_start_4735_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 1, v___x_4752_);
v___x_4754_ = v___x_4743_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_array_4734_);
lean_ctor_set(v_reuseFailAlloc_4761_, 1, v___x_4752_);
lean_ctor_set(v_reuseFailAlloc_4761_, 2, v_stop_4736_);
v___x_4754_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
lean_object* v___x_4756_; 
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 1, v___x_4754_);
lean_ctor_set(v___x_4732_, 0, v_a_4750_);
v___x_4756_ = v___x_4732_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4750_);
lean_ctor_set(v_reuseFailAlloc_4760_, 1, v___x_4754_);
v___x_4756_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
size_t v___x_4757_; size_t v___x_4758_; 
v___x_4757_ = ((size_t)1ULL);
v___x_4758_ = lean_usize_add(v_i_4720_, v___x_4757_);
v_i_4720_ = v___x_4758_;
v_b_4721_ = v___x_4756_;
goto _start;
}
}
}
else
{
lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_del_object(v___x_4743_);
lean_dec(v_stop_4736_);
lean_dec(v_start_4735_);
lean_dec_ref(v_array_4734_);
lean_del_object(v___x_4732_);
v_a_4762_ = lean_ctor_get(v___x_4749_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4749_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4749_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4749_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4775_, lean_object* v_sz_4776_, lean_object* v_i_4777_, lean_object* v_b_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
size_t v_sz_boxed_4784_; size_t v_i_boxed_4785_; lean_object* v_res_4786_; 
v_sz_boxed_4784_ = lean_unbox_usize(v_sz_4776_);
lean_dec(v_sz_4776_);
v_i_boxed_4785_ = lean_unbox_usize(v_i_4777_);
lean_dec(v_i_4777_);
v_res_4786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4775_, v_sz_boxed_4784_, v_i_boxed_4785_, v_b_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec_ref(v_as_4775_);
return v_res_4786_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4789_ = l_Lean_stringToMessageData(v___x_4788_);
return v___x_4789_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___f_4791_; 
v___x_4790_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4791_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4791_, 0, v___x_4790_);
return v___f_4791_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4793_ = l_Lean_Expr_sort___override(v___x_4792_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4794_, lean_object* v_positions_4795_, lean_object* v_brecOnConst_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v_recArgInfo_4804_; lean_object* v_indicesPos_4805_; lean_object* v_indIdx_4806_; lean_object* v_brecOn_4807_; lean_object* v___f_4808_; uint8_t v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4802_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4803_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4804_ = lean_array_get_borrowed(v___x_4802_, v_recArgInfos_4794_, v___x_4803_);
v_indicesPos_4805_ = lean_ctor_get(v_recArgInfo_4804_, 3);
v_indIdx_4806_ = lean_ctor_get(v_recArgInfo_4804_, 5);
lean_inc(v_indIdx_4806_);
v_brecOn_4807_ = lean_apply_1(v_brecOnConst_4796_, v_indIdx_4806_);
v___f_4808_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4809_ = 0;
v___x_4810_ = lean_box(v___x_4809_);
lean_inc_ref(v_brecOn_4807_);
v___x_4811_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4811_, 0, v_brecOn_4807_);
lean_closure_set(v___x_4811_, 1, v___x_4810_);
v___x_4812_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4811_, v___f_4808_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v___x_4813_; 
lean_dec_ref_known(v___x_4812_, 1);
lean_inc(v_a_4800_);
lean_inc_ref(v_a_4799_);
lean_inc(v_a_4798_);
lean_inc_ref(v_a_4797_);
v___x_4813_ = lean_infer_type(v_brecOn_4807_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v_numTypeFormers_4815_; lean_object* v___f_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; uint8_t v___x_4821_; lean_object* v___x_4822_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4814_);
lean_dec_ref_known(v___x_4813_, 1);
v_numTypeFormers_4815_ = lean_array_get_size(v_positions_4795_);
v___f_4816_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4816_, 0, v_numTypeFormers_4815_);
v___x_4817_ = lean_array_get_size(v_indicesPos_4805_);
v___x_4818_ = lean_unsigned_to_nat(1u);
v___x_4819_ = lean_nat_add(v___x_4817_, v___x_4818_);
v___x_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
v___x_4821_ = 0;
v___x_4822_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4814_, v___x_4820_, v___f_4816_, v___x_4821_, v___x_4821_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; size_t v_sz_4829_; size_t v___x_4830_; lean_object* v___x_4831_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref_known(v___x_4822_, 1);
v___x_4824_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4795_);
v___x_4825_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4826_ = lean_mk_array(v___x_4824_, v___x_4825_);
v___x_4827_ = l_Array_toSubarray___redArg(v_positions_4795_, v___x_4803_, v_numTypeFormers_4815_);
v___x_4828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v_sz_4829_ = lean_array_size(v_a_4823_);
v___x_4830_ = ((size_t)0ULL);
v___x_4831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4823_, v_sz_4829_, v___x_4830_, v___x_4828_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4823_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4840_; 
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4834_ = v___x_4831_;
v_isShared_4835_ = v_isSharedCheck_4840_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4831_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4840_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v_fst_4836_; lean_object* v___x_4838_; 
v_fst_4836_ = lean_ctor_get(v_a_4832_, 0);
lean_inc(v_fst_4836_);
lean_dec(v_a_4832_);
if (v_isShared_4835_ == 0)
{
lean_ctor_set(v___x_4834_, 0, v_fst_4836_);
v___x_4838_ = v___x_4834_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v_fst_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
v_a_4841_ = lean_ctor_get(v___x_4831_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4831_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4831_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4795_);
return v___x_4822_;
}
}
else
{
lean_object* v_a_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4856_; 
lean_dec_ref(v_positions_4795_);
v_a_4849_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4851_ = v___x_4813_;
v_isShared_4852_ = v_isSharedCheck_4856_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_a_4849_);
lean_dec(v___x_4813_);
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
else
{
lean_object* v_a_4857_; lean_object* v___x_4859_; uint8_t v_isShared_4860_; uint8_t v_isSharedCheck_4864_; 
lean_dec_ref(v_brecOn_4807_);
lean_dec_ref(v_positions_4795_);
v_a_4857_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4859_ = v___x_4812_;
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
else
{
lean_inc(v_a_4857_);
lean_dec(v___x_4812_);
v___x_4859_ = lean_box(0);
v_isShared_4860_ = v_isSharedCheck_4864_;
goto v_resetjp_4858_;
}
v_resetjp_4858_:
{
lean_object* v___x_4862_; 
if (v_isShared_4860_ == 0)
{
v___x_4862_ = v___x_4859_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
return v___x_4862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4865_, lean_object* v_positions_4866_, lean_object* v_brecOnConst_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v_res_4873_; 
v_res_4873_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4865_, v_positions_4866_, v_brecOnConst_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_);
lean_dec(v_a_4871_);
lean_dec_ref(v_a_4870_);
lean_dec(v_a_4869_);
lean_dec_ref(v_a_4868_);
lean_dec_ref(v_recArgInfos_4865_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4874_, lean_object* v_as_4875_, size_t v_sz_4876_, size_t v_i_4877_, lean_object* v_b_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v___x_4884_; 
v___x_4884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4874_, v_as_4875_, v_sz_4876_, v_i_4877_, v_b_4878_);
return v___x_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4885_, lean_object* v_as_4886_, lean_object* v_sz_4887_, lean_object* v_i_4888_, lean_object* v_b_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
size_t v_sz_boxed_4895_; size_t v_i_boxed_4896_; lean_object* v_res_4897_; 
v_sz_boxed_4895_ = lean_unbox_usize(v_sz_4887_);
lean_dec(v_sz_4887_);
v_i_boxed_4896_ = lean_unbox_usize(v_i_4888_);
lean_dec(v_i_4888_);
v_res_4897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4885_, v_as_4886_, v_sz_boxed_4895_, v_i_boxed_4896_, v_b_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
lean_dec_ref(v_as_4886_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4898_, lean_object* v_a_4899_){
_start:
{
if (lean_obj_tag(v_a_4898_) == 0)
{
lean_object* v___x_4900_; 
v___x_4900_ = l_List_reverse___redArg(v_a_4899_);
return v___x_4900_;
}
else
{
lean_object* v_head_4901_; lean_object* v_tail_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4913_; 
v_head_4901_ = lean_ctor_get(v_a_4898_, 0);
v_tail_4902_ = lean_ctor_get(v_a_4898_, 1);
v_isSharedCheck_4913_ = !lean_is_exclusive(v_a_4898_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4904_ = v_a_4898_;
v_isShared_4905_ = v_isSharedCheck_4913_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_tail_4902_);
lean_inc(v_head_4901_);
lean_dec(v_a_4898_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4913_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4910_; 
v___x_4906_ = l_Nat_reprFast(v_head_4901_);
v___x_4907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___x_4906_);
v___x_4908_ = l_Lean_MessageData_ofFormat(v___x_4907_);
if (v_isShared_4905_ == 0)
{
lean_ctor_set(v___x_4904_, 1, v_a_4899_);
lean_ctor_set(v___x_4904_, 0, v___x_4908_);
v___x_4910_ = v___x_4904_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4908_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_a_4899_);
v___x_4910_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
v_a_4898_ = v_tail_4902_;
v_a_4899_ = v___x_4910_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4914_, lean_object* v_a_4915_){
_start:
{
if (lean_obj_tag(v_a_4914_) == 0)
{
lean_object* v___x_4916_; 
v___x_4916_ = l_List_reverse___redArg(v_a_4915_);
return v___x_4916_;
}
else
{
lean_object* v_head_4917_; lean_object* v_tail_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4930_; 
v_head_4917_ = lean_ctor_get(v_a_4914_, 0);
v_tail_4918_ = lean_ctor_get(v_a_4914_, 1);
v_isSharedCheck_4930_ = !lean_is_exclusive(v_a_4914_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4920_ = v_a_4914_;
v_isShared_4921_ = v_isSharedCheck_4930_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_tail_4918_);
lean_inc(v_head_4917_);
lean_dec(v_a_4914_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4930_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4927_; 
v___x_4922_ = lean_array_to_list(v_head_4917_);
v___x_4923_ = lean_box(0);
v___x_4924_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4922_, v___x_4923_);
v___x_4925_ = l_Lean_MessageData_ofList(v___x_4924_);
if (v_isShared_4921_ == 0)
{
lean_ctor_set(v___x_4920_, 1, v_a_4915_);
lean_ctor_set(v___x_4920_, 0, v___x_4925_);
v___x_4927_ = v___x_4920_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4925_);
lean_ctor_set(v_reuseFailAlloc_4929_, 1, v_a_4915_);
v___x_4927_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
v_a_4914_ = v_tail_4918_;
v_a_4915_ = v___x_4927_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4931_, lean_object* v_v_4932_, lean_object* v_i_4933_){
_start:
{
lean_object* v___x_4934_; uint8_t v___x_4935_; 
v___x_4934_ = lean_array_get_size(v_xs_4931_);
v___x_4935_ = lean_nat_dec_lt(v_i_4933_, v___x_4934_);
if (v___x_4935_ == 0)
{
lean_object* v___x_4936_; 
lean_dec(v_i_4933_);
v___x_4936_ = lean_box(0);
return v___x_4936_;
}
else
{
lean_object* v___x_4937_; uint8_t v___x_4938_; 
v___x_4937_ = lean_array_fget_borrowed(v_xs_4931_, v_i_4933_);
v___x_4938_ = lean_nat_dec_eq(v___x_4937_, v_v_4932_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = lean_unsigned_to_nat(1u);
v___x_4940_ = lean_nat_add(v_i_4933_, v___x_4939_);
lean_dec(v_i_4933_);
v_i_4933_ = v___x_4940_;
goto _start;
}
else
{
lean_object* v___x_4942_; 
v___x_4942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4942_, 0, v_i_4933_);
return v___x_4942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4943_, lean_object* v_v_4944_, lean_object* v_i_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4943_, v_v_4944_, v_i_4945_);
lean_dec(v_v_4944_);
lean_dec_ref(v_xs_4943_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4947_, lean_object* v_v_4948_){
_start:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; 
v___x_4949_ = lean_unsigned_to_nat(0u);
v___x_4950_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4947_, v_v_4948_, v___x_4949_);
return v___x_4950_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4951_, lean_object* v_v_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4951_, v_v_4952_);
lean_dec(v_v_4952_);
lean_dec_ref(v_xs_4951_);
return v_res_4953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4957_, lean_object* v_as_4958_, size_t v_sz_4959_, size_t v_i_4960_, lean_object* v_b_4961_){
_start:
{
uint8_t v___x_4962_; 
v___x_4962_ = lean_usize_dec_lt(v_i_4960_, v_sz_4959_);
if (v___x_4962_ == 0)
{
lean_inc_ref(v_b_4961_);
return v_b_4961_;
}
else
{
lean_object* v___x_4963_; lean_object* v_a_4964_; lean_object* v___x_4965_; 
v___x_4963_ = lean_box(0);
v_a_4964_ = lean_array_uget_borrowed(v_as_4958_, v_i_4960_);
v___x_4965_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4964_, v_fnIdx_4957_);
if (lean_obj_tag(v___x_4965_) == 0)
{
lean_object* v___x_4966_; size_t v___x_4967_; size_t v___x_4968_; 
v___x_4966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4967_ = ((size_t)1ULL);
v___x_4968_ = lean_usize_add(v_i_4960_, v___x_4967_);
v_i_4960_ = v___x_4968_;
v_b_4961_ = v___x_4966_;
goto _start;
}
else
{
lean_object* v_val_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4981_; 
v_val_4970_ = lean_ctor_get(v___x_4965_, 0);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4965_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4972_ = v___x_4965_;
v_isShared_4973_ = v_isSharedCheck_4981_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_val_4970_);
lean_dec(v___x_4965_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4981_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4977_; 
v___x_4974_ = lean_array_get_size(v_a_4964_);
v___x_4975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4974_);
lean_ctor_set(v___x_4975_, 1, v_val_4970_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 0, v___x_4975_);
v___x_4977_ = v___x_4972_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4975_);
v___x_4977_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___x_4978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
v___x_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
lean_ctor_set(v___x_4979_, 1, v___x_4963_);
return v___x_4979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4982_, lean_object* v_as_4983_, lean_object* v_sz_4984_, lean_object* v_i_4985_, lean_object* v_b_4986_){
_start:
{
size_t v_sz_boxed_4987_; size_t v_i_boxed_4988_; lean_object* v_res_4989_; 
v_sz_boxed_4987_ = lean_unbox_usize(v_sz_4984_);
lean_dec(v_sz_4984_);
v_i_boxed_4988_ = lean_unbox_usize(v_i_4985_);
lean_dec(v_i_4985_);
v_res_4989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4982_, v_as_4983_, v_sz_boxed_4987_, v_i_boxed_4988_, v_b_4986_);
lean_dec_ref(v_b_4986_);
lean_dec_ref(v_as_4983_);
lean_dec(v_fnIdx_4982_);
return v_res_4989_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4991_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4992_ = l_Lean_stringToMessageData(v___x_4991_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4993_, lean_object* v_positions_4994_, lean_object* v_fnIdx_4995_, lean_object* v_brecOnConst_4996_, lean_object* v_packedFArgs_4997_, lean_object* v_funTypes_4998_, lean_object* v_ys_4999_, lean_object* v___value_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v___y_5007_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v___y_5010_; lean_object* v___x_5024_; lean_object* v_fst_5025_; lean_object* v_snd_5026_; lean_object* v___x_5027_; size_t v_sz_5028_; size_t v___x_5029_; lean_object* v___x_5030_; lean_object* v_fst_5031_; 
lean_inc_ref(v_ys_4999_);
lean_inc_ref(v_recArgInfo_4993_);
v___x_5024_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4993_, v_ys_4999_);
v_fst_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_fst_5025_);
v_snd_5026_ = lean_ctor_get(v___x_5024_, 1);
lean_inc(v_snd_5026_);
lean_dec_ref(v___x_5024_);
v___x_5027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5028_ = lean_array_size(v_positions_4994_);
v___x_5029_ = ((size_t)0ULL);
v___x_5030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4995_, v_positions_4994_, v_sz_5028_, v___x_5029_, v___x_5027_);
v_fst_5031_ = lean_ctor_get(v___x_5030_, 0);
lean_inc(v_fst_5031_);
lean_dec_ref(v___x_5030_);
if (lean_obj_tag(v_fst_5031_) == 0)
{
lean_dec(v_snd_5026_);
lean_dec(v_fst_5025_);
lean_dec_ref(v_ys_4999_);
lean_dec_ref(v_brecOnConst_4996_);
lean_dec_ref(v_recArgInfo_4993_);
v___y_5007_ = v___y_5001_;
v___y_5008_ = v___y_5002_;
v___y_5009_ = v___y_5003_;
v___y_5010_ = v___y_5004_;
goto v___jp_5006_;
}
else
{
lean_object* v_val_5032_; 
v_val_5032_ = lean_ctor_get(v_fst_5031_, 0);
lean_inc(v_val_5032_);
lean_dec_ref_known(v_fst_5031_, 1);
if (lean_obj_tag(v_val_5032_) == 1)
{
lean_object* v_val_5033_; lean_object* v_fst_5034_; lean_object* v_snd_5035_; lean_object* v_indIdx_5036_; lean_object* v_brecOn_5037_; lean_object* v_brecOn_5038_; lean_object* v_brecOn_5039_; lean_object* v___x_5040_; 
lean_dec(v_fnIdx_4995_);
lean_dec_ref(v_positions_4994_);
v_val_5033_ = lean_ctor_get(v_val_5032_, 0);
lean_inc(v_val_5033_);
lean_dec_ref_known(v_val_5032_, 1);
v_fst_5034_ = lean_ctor_get(v_val_5033_, 0);
lean_inc(v_fst_5034_);
v_snd_5035_ = lean_ctor_get(v_val_5033_, 1);
lean_inc(v_snd_5035_);
lean_dec(v_val_5033_);
v_indIdx_5036_ = lean_ctor_get(v_recArgInfo_4993_, 5);
lean_inc(v_indIdx_5036_);
lean_dec_ref(v_recArgInfo_4993_);
v_brecOn_5037_ = lean_apply_1(v_brecOnConst_4996_, v_indIdx_5036_);
v_brecOn_5038_ = l_Lean_mkAppN(v_brecOn_5037_, v_fst_5025_);
lean_dec(v_fst_5025_);
v_brecOn_5039_ = l_Lean_mkAppN(v_brecOn_5038_, v_packedFArgs_4997_);
v___x_5040_ = l_Lean_Meta_PProdN_projM(v_fst_5034_, v_snd_5035_, v_brecOn_5039_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
lean_dec(v_snd_5035_);
lean_dec(v_fst_5034_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5042_; uint8_t v___x_5043_; uint8_t v___x_5044_; lean_object* v___x_5045_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
lean_dec_ref_known(v___x_5040_, 1);
v___x_5042_ = l_Lean_mkAppN(v_a_5041_, v_snd_5026_);
lean_dec(v_snd_5026_);
v___x_5043_ = 1;
v___x_5044_ = 1;
v___x_5045_ = l_Lean_Meta_mkLetFVars(v_funTypes_4998_, v___x_5042_, v___x_5043_, v___x_5043_, v___x_5044_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; uint8_t v___x_5047_; lean_object* v___x_5048_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5046_);
lean_dec_ref_known(v___x_5045_, 1);
v___x_5047_ = 0;
v___x_5048_ = l_Lean_Meta_mkLambdaFVars(v_ys_4999_, v_a_5046_, v___x_5047_, v___x_5043_, v___x_5047_, v___x_5043_, v___x_5044_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_);
lean_dec_ref(v_ys_4999_);
return v___x_5048_;
}
else
{
lean_dec_ref(v_ys_4999_);
return v___x_5045_;
}
}
else
{
lean_dec(v_snd_5026_);
lean_dec_ref(v_ys_4999_);
return v___x_5040_;
}
}
else
{
lean_dec(v_val_5032_);
lean_dec(v_snd_5026_);
lean_dec(v_fst_5025_);
lean_dec_ref(v_ys_4999_);
lean_dec_ref(v_brecOnConst_4996_);
lean_dec_ref(v_recArgInfo_4993_);
v___y_5007_ = v___y_5001_;
v___y_5008_ = v___y_5002_;
v___y_5009_ = v___y_5003_;
v___y_5010_ = v___y_5004_;
goto v___jp_5006_;
}
}
v___jp_5006_:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5011_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_5012_ = l_Nat_reprFast(v_fnIdx_4995_);
v___x_5013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5012_);
v___x_5014_ = l_Lean_MessageData_ofFormat(v___x_5013_);
v___x_5015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5011_);
lean_ctor_set(v___x_5015_, 1, v___x_5014_);
v___x_5016_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5015_);
lean_ctor_set(v___x_5017_, 1, v___x_5016_);
v___x_5018_ = lean_array_to_list(v_positions_4994_);
v___x_5019_ = lean_box(0);
v___x_5020_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5018_, v___x_5019_);
v___x_5021_ = l_Lean_MessageData_ofList(v___x_5020_);
v___x_5022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5017_);
lean_ctor_set(v___x_5022_, 1, v___x_5021_);
v___x_5023_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5022_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_);
return v___x_5023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5049_, lean_object* v_positions_5050_, lean_object* v_fnIdx_5051_, lean_object* v_brecOnConst_5052_, lean_object* v_packedFArgs_5053_, lean_object* v_funTypes_5054_, lean_object* v_ys_5055_, lean_object* v___value_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5049_, v_positions_5050_, v_fnIdx_5051_, v_brecOnConst_5052_, v_packedFArgs_5053_, v_funTypes_5054_, v_ys_5055_, v___value_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
lean_dec(v___y_5060_);
lean_dec_ref(v___y_5059_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec_ref(v___value_5056_);
lean_dec_ref(v_funTypes_5054_);
lean_dec_ref(v_packedFArgs_5053_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5063_, lean_object* v_fnIdx_5064_, lean_object* v_brecOnConst_5065_, lean_object* v_packedFArgs_5066_, lean_object* v_funTypes_5067_, lean_object* v_recArgInfo_5068_, lean_object* v_value_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v___f_5075_; uint8_t v___x_5076_; lean_object* v___x_5077_; 
v___f_5075_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5075_, 0, v_recArgInfo_5068_);
lean_closure_set(v___f_5075_, 1, v_positions_5063_);
lean_closure_set(v___f_5075_, 2, v_fnIdx_5064_);
lean_closure_set(v___f_5075_, 3, v_brecOnConst_5065_);
lean_closure_set(v___f_5075_, 4, v_packedFArgs_5066_);
lean_closure_set(v___f_5075_, 5, v_funTypes_5067_);
v___x_5076_ = 0;
v___x_5077_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5069_, v___f_5075_, v___x_5076_, v_a_5070_, v_a_5071_, v_a_5072_, v_a_5073_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5078_, lean_object* v_fnIdx_5079_, lean_object* v_brecOnConst_5080_, lean_object* v_packedFArgs_5081_, lean_object* v_funTypes_5082_, lean_object* v_recArgInfo_5083_, lean_object* v_value_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_){
_start:
{
lean_object* v_res_5090_; 
v_res_5090_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5078_, v_fnIdx_5079_, v_brecOnConst_5080_, v_packedFArgs_5081_, v_funTypes_5082_, v_recArgInfo_5083_, v_value_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_);
lean_dec(v_a_5088_);
lean_dec_ref(v_a_5087_);
lean_dec(v_a_5086_);
lean_dec_ref(v_a_5085_);
return v_res_5090_;
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
