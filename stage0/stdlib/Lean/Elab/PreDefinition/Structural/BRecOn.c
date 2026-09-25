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
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_IndGroupInfo_brecOnName(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_projM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited___redArg();
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "belowType: "};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18;
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
static double l_Lean_Elab_Structural_toBelow___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected type of `brecOn` argument"};
static const lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object*, lean_object*);
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
lean_object* v_ref_360_; lean_object* v___x_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_407_; 
v_ref_360_ = lean_ctor_get(v___y_357_, 2);
v___x_361_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_407_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_407_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_407_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v_traceState_367_; lean_object* v_env_368_; lean_object* v_nextMacroScope_369_; lean_object* v_ngen_370_; lean_object* v_auxDeclNGen_371_; lean_object* v_cache_372_; lean_object* v_recordedDeps_373_; lean_object* v_messages_374_; lean_object* v_infoState_375_; lean_object* v_snapshotTasks_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_406_; 
v___x_366_ = lean_st_ref_take(v___y_358_);
v_traceState_367_ = lean_ctor_get(v___x_366_, 4);
v_env_368_ = lean_ctor_get(v___x_366_, 0);
v_nextMacroScope_369_ = lean_ctor_get(v___x_366_, 1);
v_ngen_370_ = lean_ctor_get(v___x_366_, 2);
v_auxDeclNGen_371_ = lean_ctor_get(v___x_366_, 3);
v_cache_372_ = lean_ctor_get(v___x_366_, 5);
v_recordedDeps_373_ = lean_ctor_get(v___x_366_, 6);
v_messages_374_ = lean_ctor_get(v___x_366_, 7);
v_infoState_375_ = lean_ctor_get(v___x_366_, 8);
v_snapshotTasks_376_ = lean_ctor_get(v___x_366_, 9);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_406_ == 0)
{
v___x_378_ = v___x_366_;
v_isShared_379_ = v_isSharedCheck_406_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_snapshotTasks_376_);
lean_inc(v_infoState_375_);
lean_inc(v_messages_374_);
lean_inc(v_recordedDeps_373_);
lean_inc(v_cache_372_);
lean_inc(v_traceState_367_);
lean_inc(v_auxDeclNGen_371_);
lean_inc(v_ngen_370_);
lean_inc(v_nextMacroScope_369_);
lean_inc(v_env_368_);
lean_dec(v___x_366_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_406_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
uint64_t v_tid_380_; lean_object* v_traces_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_405_; 
v_tid_380_ = lean_ctor_get_uint64(v_traceState_367_, sizeof(void*)*1);
v_traces_381_ = lean_ctor_get(v_traceState_367_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_traceState_367_);
if (v_isSharedCheck_405_ == 0)
{
v___x_383_ = v_traceState_367_;
v_isShared_384_ = v_isSharedCheck_405_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_traces_381_);
lean_dec(v_traceState_367_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_405_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; double v___x_387_; uint8_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_385_ = lean_box(0);
v___x_386_ = lean_box(0);
v___x_387_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_388_ = 0;
v___x_389_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_390_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_390_, 0, v_cls_353_);
lean_ctor_set(v___x_390_, 1, v___x_386_);
lean_ctor_set(v___x_390_, 2, v___x_389_);
lean_ctor_set_float(v___x_390_, sizeof(void*)*3, v___x_387_);
lean_ctor_set_float(v___x_390_, sizeof(void*)*3 + 8, v___x_387_);
lean_ctor_set_uint8(v___x_390_, sizeof(void*)*3 + 16, v___x_388_);
v___x_391_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_392_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v_a_362_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
lean_inc(v_ref_360_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_ref_360_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = l_Lean_PersistentArray_push___redArg(v_traces_381_, v___x_393_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_394_);
v___x_396_ = v___x_383_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_394_);
lean_ctor_set_uint64(v_reuseFailAlloc_404_, sizeof(void*)*1, v_tid_380_);
v___x_396_ = v_reuseFailAlloc_404_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_398_; 
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 4, v___x_396_);
v___x_398_ = v___x_378_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_env_368_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_nextMacroScope_369_);
lean_ctor_set(v_reuseFailAlloc_403_, 2, v_ngen_370_);
lean_ctor_set(v_reuseFailAlloc_403_, 3, v_auxDeclNGen_371_);
lean_ctor_set(v_reuseFailAlloc_403_, 4, v___x_396_);
lean_ctor_set(v_reuseFailAlloc_403_, 5, v_cache_372_);
lean_ctor_set(v_reuseFailAlloc_403_, 6, v_recordedDeps_373_);
lean_ctor_set(v_reuseFailAlloc_403_, 7, v_messages_374_);
lean_ctor_set(v_reuseFailAlloc_403_, 8, v_infoState_375_);
lean_ctor_set(v_reuseFailAlloc_403_, 9, v_snapshotTasks_376_);
v___x_398_ = v_reuseFailAlloc_403_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_st_ref_put(v___y_358_, v___x_398_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_385_);
v___x_401_ = v___x_364_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_385_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object* v_cls_408_, lean_object* v_msg_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_408_, v_msg_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v_a_422_, lean_object* v_C_423_, lean_object* v_cls_424_, lean_object* v___f_425_, lean_object* v_belowDict_426_, lean_object* v_F_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_){
_start:
{
lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___x_502_; 
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
v___x_502_ = lean_apply_5(v___f_425_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, lean_box(0));
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
goto v___jp_466_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_426_);
v___x_506_ = l_Lean_indentExpr(v_belowDict_426_);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_inc(v_cls_424_);
v___x_508_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_424_, v___x_507_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_dec_ref_known(v___x_508_, 1);
goto v___jp_466_;
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_F_427_);
lean_dec_ref(v_belowDict_426_);
lean_dec(v_cls_424_);
lean_dec_ref(v_a_422_);
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
lean_dec_ref(v_F_427_);
lean_dec_ref(v_belowDict_426_);
lean_dec(v_cls_424_);
lean_dec_ref(v_a_422_);
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
v___jp_433_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_isExprDefEq(v___y_434_, v_a_422_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_457_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_457_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_457_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_457_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
uint8_t v___x_444_; 
v___x_444_ = lean_unbox(v_a_440_);
lean_dec(v_a_440_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_del_object(v___x_442_);
lean_dec_ref(v_F_427_);
v___x_445_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_435_, v___y_436_, v___y_437_, v___y_438_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
else
{
lean_object* v___x_455_; 
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v_F_427_);
v___x_455_ = v___x_442_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_F_427_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v_F_427_);
v_a_458_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_439_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_439_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
v___jp_466_:
{
if (lean_obj_tag(v_belowDict_426_) == 5)
{
lean_object* v_fn_467_; lean_object* v_arg_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
lean_dec(v_cls_424_);
v_fn_467_ = lean_ctor_get(v_belowDict_426_, 0);
lean_inc_ref(v_fn_467_);
v_arg_468_ = lean_ctor_get(v_belowDict_426_, 1);
lean_inc_ref(v_arg_468_);
lean_dec_ref_known(v_belowDict_426_, 2);
v___x_469_ = l_Lean_Expr_getAppFn(v_fn_467_);
lean_dec_ref(v_fn_467_);
v___x_470_ = lean_expr_eqv(v___x_469_, v_C_423_);
lean_dec_ref(v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_arg_468_);
lean_dec_ref(v_F_427_);
lean_dec_ref(v_a_422_);
v___x_471_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_428_, v___y_429_, v___y_430_, v___y_431_);
v_a_472_ = lean_ctor_get(v___x_471_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_471_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_471_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
v___y_434_ = v_arg_468_;
v___y_435_ = v___y_428_;
v___y_436_ = v___y_429_;
v___y_437_ = v___y_430_;
v___y_438_ = v___y_431_;
goto v___jp_433_;
}
}
else
{
lean_object* v_toCold_480_; lean_object* v_options_481_; uint8_t v_hasTrace_482_; 
lean_dec_ref(v_F_427_);
lean_dec_ref(v_a_422_);
v_toCold_480_ = lean_ctor_get(v___y_430_, 0);
v_options_481_ = lean_ctor_get(v_toCold_480_, 2);
v_hasTrace_482_ = lean_ctor_get_uint8(v_options_481_, sizeof(void*)*1);
if (v_hasTrace_482_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_belowDict_426_);
lean_dec(v_cls_424_);
v___x_483_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_428_, v___y_429_, v___y_430_, v___y_431_);
return v___x_483_;
}
else
{
lean_object* v_inheritedTraceOptions_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_inheritedTraceOptions_484_ = lean_ctor_get(v_toCold_480_, 11);
v___x_485_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_424_);
v___x_486_ = l_Lean_Name_append(v___x_485_, v_cls_424_);
v___x_487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_484_, v_options_481_, v___x_486_);
lean_dec(v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_dec_ref(v_belowDict_426_);
lean_dec(v_cls_424_);
v___x_488_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_428_, v___y_429_, v___y_430_, v___y_431_);
return v___x_488_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_489_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_490_ = l_Lean_indentExpr(v_belowDict_426_);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_424_, v___x_491_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___x_493_; 
lean_dec_ref_known(v___x_492_, 1);
v___x_493_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_428_, v___y_429_, v___y_430_, v___y_431_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v_a_525_, lean_object* v_C_526_, lean_object* v_cls_527_, lean_object* v___f_528_, lean_object* v_belowDict_529_, lean_object* v_F_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v_a_525_, v_C_526_, v_cls_527_, v___f_528_, v_belowDict_529_, v_F_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v_C_526_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_539_, lean_object* v_C_540_, lean_object* v_cls_541_, lean_object* v___f_542_, lean_object* v_F_543_, lean_object* v_xs_544_, lean_object* v_belowDict_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
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
lean_closure_set(v___f_554_, 0, v_a_553_);
lean_closure_set(v___f_554_, 1, v_C_540_);
lean_closure_set(v___f_554_, 2, v_cls_541_);
lean_closure_set(v___f_554_, 3, v___f_542_);
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
lean_dec_ref(v___f_542_);
lean_dec(v_cls_541_);
lean_dec_ref(v_C_540_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_585_, lean_object* v_C_586_, lean_object* v_cls_587_, lean_object* v___f_588_, lean_object* v_F_589_, lean_object* v_xs_590_, lean_object* v_belowDict_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_585_, v_C_586_, v_cls_587_, v___f_588_, v_F_589_, v_xs_590_, v_belowDict_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v_arg_601_, lean_object* v_C_602_, lean_object* v_cls_603_, lean_object* v___f_604_, lean_object* v_belowDict_605_, lean_object* v_F_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v___f_612_; lean_object* v___x_616_; 
lean_inc_ref(v___f_604_);
lean_inc(v_cls_603_);
v___f_612_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_612_, 0, v_arg_601_);
lean_closure_set(v___f_612_, 1, v_C_602_);
lean_closure_set(v___f_612_, 2, v_cls_603_);
lean_closure_set(v___f_612_, 3, v___f_604_);
lean_closure_set(v___f_612_, 4, v_F_606_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
v___x_616_ = lean_apply_5(v___f_604_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, lean_box(0));
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; uint8_t v___x_618_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = lean_unbox(v_a_617_);
lean_dec(v_a_617_);
if (v___x_618_ == 0)
{
lean_dec(v_cls_603_);
goto v___jp_613_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_619_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_605_);
v___x_620_ = l_Lean_indentExpr(v_belowDict_605_);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_603_, v___x_621_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_dec_ref_known(v___x_622_, 1);
goto v___jp_613_;
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v___f_612_);
lean_dec_ref(v_belowDict_605_);
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v___f_612_);
lean_dec_ref(v_belowDict_605_);
lean_dec(v_cls_603_);
v_a_631_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_616_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_616_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
v___jp_613_:
{
uint8_t v___x_614_; lean_object* v___x_615_; 
v___x_614_ = 0;
v___x_615_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_605_, v___f_612_, v___x_614_, v___x_614_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v_arg_639_, lean_object* v_C_640_, lean_object* v_cls_641_, lean_object* v___f_642_, lean_object* v_belowDict_643_, lean_object* v_F_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v_arg_639_, v_C_640_, v_cls_641_, v___f_642_, v_belowDict_643_, v_F_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_650_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_665_ = l_Lean_stringToMessageData(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_666_, lean_object* v_belowDict_667_, lean_object* v_arg_668_, lean_object* v_F_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_cls_675_; lean_object* v___f_676_; lean_object* v___f_677_; lean_object* v___x_678_; lean_object* v_a_679_; uint8_t v___x_680_; 
v_cls_675_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_676_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
lean_inc_ref(v_arg_668_);
v___f_677_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_677_, 0, v_arg_668_);
lean_closure_set(v___f_677_, 1, v_C_666_);
lean_closure_set(v___f_677_, 2, v_cls_675_);
lean_closure_set(v___f_677_, 3, v___f_676_);
v___x_678_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_675_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref(v___x_678_);
v___x_680_ = lean_unbox(v_a_679_);
lean_dec(v_a_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_dec_ref(v_arg_668_);
v___x_681_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_667_, v_F_669_, v___f_677_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_681_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_682_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_667_);
v___x_683_ = l_Lean_indentExpr(v_belowDict_667_);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_indentExpr(v_arg_668_);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_675_, v___x_688_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_690_; 
lean_dec_ref_known(v___x_689_, 1);
v___x_690_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_667_, v_F_669_, v___f_677_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
return v___x_690_;
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec_ref(v___f_677_);
lean_dec_ref(v_F_669_);
lean_dec_ref(v_belowDict_667_);
v_a_691_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_689_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_699_, lean_object* v_belowDict_700_, lean_object* v_arg_701_, lean_object* v_F_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_699_, v_belowDict_700_, v_arg_701_, v_F_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v_t_709_, lean_object* v_x_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v_t_709_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v_t_717_, lean_object* v_x_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v_t_717_, v_x_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec_ref(v_x_718_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___f_734_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_734_, 0, v_t_728_);
v___x_735_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1));
v___x_736_ = l_Lean_Core_mkFreshUserName(v___x_735_, v___y_731_, v___y_732_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_a_737_);
lean_ctor_set(v___x_741_, 1, v___f_734_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v___f_734_);
v_a_746_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_736_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_736_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v___x_761_, lean_object* v_a_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_array_set(v___y_764_, v_a_762_, v___x_761_);
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v___x_773_, lean_object* v_a_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v___x_773_, v_a_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v_a_774_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_783_, lean_object* v_a_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_snd_792_; lean_object* v_fst_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_844_; 
v_snd_792_ = lean_ctor_get(v___y_786_, 1);
v_fst_793_ = lean_ctor_get(v___y_786_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___y_786_);
if (v_isSharedCheck_844_ == 0)
{
v___x_795_ = v___y_786_;
v_isShared_796_ = v_isSharedCheck_844_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_792_);
lean_inc(v_fst_793_);
lean_dec(v___y_786_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_844_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_array_797_; lean_object* v_start_798_; lean_object* v_stop_799_; uint8_t v___x_800_; 
v_array_797_ = lean_ctor_get(v_snd_792_, 0);
v_start_798_ = lean_ctor_get(v_snd_792_, 1);
v_stop_799_ = lean_ctor_get(v_snd_792_, 2);
v___x_800_ = lean_nat_dec_lt(v_start_798_, v_stop_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_802_; 
lean_dec_ref(v_a_784_);
lean_dec_ref(v___x_783_);
if (v_isShared_796_ == 0)
{
v___x_802_ = v___x_795_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_fst_793_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_snd_792_);
v___x_802_ = v_reuseFailAlloc_805_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
else
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_840_; 
lean_inc(v_stop_799_);
lean_inc(v_start_798_);
lean_inc_ref(v_array_797_);
v_isSharedCheck_840_ = !lean_is_exclusive(v_snd_792_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; 
v_unused_841_ = lean_ctor_get(v_snd_792_, 2);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_snd_792_, 1);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_snd_792_, 0);
lean_dec(v_unused_843_);
v___x_807_ = v_snd_792_;
v_isShared_808_ = v_isSharedCheck_840_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_snd_792_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_840_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
v___x_809_ = lean_array_fget_borrowed(v_array_797_, v_start_798_);
lean_inc(v___x_809_);
v___f_810_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_810_, 0, v___x_809_);
v___x_811_ = lean_unsigned_to_nat(1u);
v___x_812_ = lean_nat_add(v_start_798_, v___x_811_);
lean_dec(v_start_798_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_812_);
v___x_814_ = v___x_807_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_array_797_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_839_, 2, v_stop_799_);
v___x_814_ = v_reuseFailAlloc_839_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
size_t v_sz_815_; size_t v___x_816_; lean_object* v___x_9002__overap_817_; lean_object* v___x_818_; 
v_sz_815_ = lean_array_size(v_a_784_);
v___x_816_ = ((size_t)0ULL);
v___x_9002__overap_817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_783_, v_a_784_, v___f_810_, v_sz_815_, v___x_816_, v_fst_793_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
v___x_818_ = lean_apply_5(v___x_9002__overap_817_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, lean_box(0));
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_830_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_830_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_830_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_830_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___x_814_);
lean_ctor_set(v___x_795_, 0, v_a_819_);
v___x_824_ = v___x_795_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_819_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_814_);
v___x_824_ = v_reuseFailAlloc_829_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_825_);
v___x_827_ = v___x_821_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v___x_814_);
lean_del_object(v___x_795_);
v_a_831_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_818_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_818_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_845_, lean_object* v_a_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_845_, v_a_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_toCold_861_; lean_object* v_options_862_; uint8_t v_hasTrace_863_; 
v_toCold_861_ = lean_ctor_get(v___y_858_, 0);
v_options_862_ = lean_ctor_get(v_toCold_861_, 2);
v_hasTrace_863_ = lean_ctor_get_uint8(v_options_862_, sizeof(void*)*1);
if (v_hasTrace_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v___x_855_);
v___x_864_ = lean_box(v_hasTrace_863_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
else
{
lean_object* v_inheritedTraceOptions_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_inheritedTraceOptions_866_ = lean_ctor_get(v_toCold_861_, 11);
v___x_867_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_868_ = l_Lean_Name_append(v___x_867_, v___x_855_);
v___x_869_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_866_, v_options_862_, v___x_868_);
lean_dec(v___x_868_);
v___x_870_ = lean_box(v___x_869_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_878_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_890_, lean_object* v___x_891_, lean_object* v_positions_892_, lean_object* v_a_893_, lean_object* v___x_894_, lean_object* v___x_895_, lean_object* v_k_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_toMonadRef_899_, lean_object* v___x_900_, lean_object* v___f_901_, lean_object* v_Cs_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_9038__overap_909_; lean_object* v___x_910_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_902_);
lean_inc_ref(v___x_890_);
v___x_9038__overap_909_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_890_, v___x_891_, v___x_908_, v_positions_892_, v_a_893_, v_Cs_902_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
v___x_910_ = lean_apply_5(v___x_9038__overap_909_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, lean_box(0));
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___x_954_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = l_Lean_mkAppN(v___x_894_, v_a_911_);
lean_dec(v_a_911_);
v___x_913_ = l_Subarray_copy___redArg(v___x_895_);
v___x_914_ = l_Lean_mkAppN(v___x_912_, v___x_913_);
lean_dec_ref(v___x_913_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
v___x_954_ = lean_apply_5(v___f_901_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, lean_box(0));
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; uint8_t v___x_956_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = lean_unbox(v_a_955_);
lean_dec(v_a_955_);
if (v___x_956_ == 0)
{
v___y_916_ = v___y_903_;
v___y_917_ = v___y_904_;
v___y_918_ = v___y_905_;
v___y_919_ = v___y_906_;
goto v___jp_915_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_9089__overap_968_; lean_object* v___x_969_; 
v___x_957_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_902_);
v___x_958_ = lean_array_to_list(v_Cs_902_);
v___x_959_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_960_ = lean_box(0);
v___x_961_ = l_List_mapTR_loop___redArg(v___x_959_, v___x_958_, v___x_960_);
v___x_962_ = l_Lean_MessageData_ofList(v___x_961_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_957_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
lean_inc_ref(v___x_914_);
v___x_966_ = l_Lean_indentExpr(v___x_914_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_inc(v___x_897_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v_toMonadRef_899_);
lean_inc_ref(v___x_898_);
lean_inc_ref(v___x_890_);
v___x_9089__overap_968_ = l_Lean_addTrace___redArg(v___x_890_, v___x_898_, v_toMonadRef_899_, v___x_900_, v___x_897_, v___x_967_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
v___x_969_ = lean_apply_5(v___x_9089__overap_968_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, lean_box(0));
if (lean_obj_tag(v___x_969_) == 0)
{
lean_dec_ref_known(v___x_969_, 1);
v___y_916_ = v___y_903_;
v___y_917_ = v___y_904_;
v___y_918_ = v___y_905_;
v___y_919_ = v___y_906_;
goto v___jp_915_;
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec_ref(v___x_914_);
lean_dec_ref(v_Cs_902_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v_k_896_);
lean_dec_ref(v___x_890_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v___x_914_);
lean_dec_ref(v_Cs_902_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v_k_896_);
lean_dec_ref(v___x_890_);
v_a_978_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_954_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_954_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
v___jp_915_:
{
lean_object* v_toCold_920_; lean_object* v_options_921_; uint8_t v_hasTrace_922_; 
v_toCold_920_ = lean_ctor_get(v___y_918_, 0);
v_options_921_ = lean_ctor_get(v_toCold_920_, 2);
v_hasTrace_922_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v___x_890_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
v___x_923_ = lean_apply_7(v_k_896_, v_Cs_902_, v___x_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
return v___x_923_;
}
else
{
lean_object* v_inheritedTraceOptions_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_inheritedTraceOptions_924_ = lean_ctor_get(v_toCold_920_, 11);
v___x_925_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_897_);
v___x_926_ = l_Lean_Name_append(v___x_925_, v___x_897_);
v___x_927_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_924_, v_options_921_, v___x_926_);
lean_dec(v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v___x_890_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
v___x_928_ = lean_apply_7(v_k_896_, v_Cs_902_, v___x_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
return v___x_928_;
}
else
{
lean_object* v___x_929_; 
lean_inc_ref(v___x_914_);
v___x_929_ = l_Lean_Meta_isTypeCorrect(v___x_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
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
if (v___x_927_ == 0)
{
lean_object* v___x_932_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v___x_890_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
v___x_932_ = lean_apply_7(v_k_896_, v_Cs_902_, v___x_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_9062__overap_934_; lean_object* v___x_935_; 
v___x_933_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_9062__overap_934_ = l_Lean_addTrace___redArg(v___x_890_, v___x_898_, v_toMonadRef_899_, v___x_900_, v___x_897_, v___x_933_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
v___x_935_ = lean_apply_5(v___x_9062__overap_934_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
lean_dec_ref_known(v___x_935_, 1);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
v___x_936_ = lean_apply_7(v_k_896_, v_Cs_902_, v___x_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
return v___x_936_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___x_914_);
lean_dec_ref(v_Cs_902_);
lean_dec_ref(v_k_896_);
v_a_937_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_935_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v___x_890_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
v___x_945_ = lean_apply_7(v_k_896_, v_Cs_902_, v___x_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, lean_box(0));
return v___x_945_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___x_914_);
lean_dec_ref(v_Cs_902_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v_k_896_);
lean_dec_ref(v___x_890_);
v_a_946_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_929_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_929_);
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
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_dec_ref(v_Cs_902_);
lean_dec_ref(v___f_901_);
lean_dec_ref(v___x_900_);
lean_dec_ref(v_toMonadRef_899_);
lean_dec_ref(v___x_898_);
lean_dec(v___x_897_);
lean_dec_ref(v_k_896_);
lean_dec_ref(v___x_895_);
lean_dec_ref(v___x_894_);
lean_dec_ref(v___x_890_);
v_a_986_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_910_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_910_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_994_ = _args[0];
lean_object* v___x_995_ = _args[1];
lean_object* v_positions_996_ = _args[2];
lean_object* v_a_997_ = _args[3];
lean_object* v___x_998_ = _args[4];
lean_object* v___x_999_ = _args[5];
lean_object* v_k_1000_ = _args[6];
lean_object* v___x_1001_ = _args[7];
lean_object* v___x_1002_ = _args[8];
lean_object* v_toMonadRef_1003_ = _args[9];
lean_object* v___x_1004_ = _args[10];
lean_object* v___f_1005_ = _args[11];
lean_object* v_Cs_1006_ = _args[12];
lean_object* v___y_1007_ = _args[13];
lean_object* v___y_1008_ = _args[14];
lean_object* v___y_1009_ = _args[15];
lean_object* v___y_1010_ = _args[16];
lean_object* v___y_1011_ = _args[17];
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_994_, v___x_995_, v_positions_996_, v_a_997_, v___x_998_, v___x_999_, v_k_1000_, v___x_1001_, v___x_1002_, v_toMonadRef_1003_, v___x_1004_, v___f_1005_, v_Cs_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1012_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_unsigned_to_nat(37u);
v___x_1014_ = l_Lean_Level_ofNat(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1016_ = l_Lean_Expr_sort___override(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1023_, lean_object* v___x_1024_, lean_object* v___f_1025_, lean_object* v___f_1026_, lean_object* v___x_1027_, lean_object* v_numTypeFormers_1028_, lean_object* v___x_1029_, lean_object* v_k_1030_, lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v_toMonadRef_1033_, lean_object* v___x_1034_, lean_object* v___f_1035_, lean_object* v_numIndParams_1036_, lean_object* v_a_1037_, lean_object* v_f_1038_, lean_object* v_args_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v_lower_1095_; lean_object* v_upper_1096_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___x_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1162_ = lean_nat_add(v_numIndParams_1036_, v_numTypeFormers_1028_);
v___x_1163_ = lean_array_get_size(v_args_1039_);
v___x_1164_ = lean_nat_dec_lt(v___x_1162_, v___x_1163_);
lean_dec(v___x_1162_);
if (v___x_1164_ == 0)
{
lean_object* v___x_1165_; 
lean_dec_ref(v_args_1039_);
lean_dec_ref(v_f_1038_);
lean_dec(v_numIndParams_1036_);
lean_dec_ref(v_k_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v_numTypeFormers_1028_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v_positions_1023_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
v___x_1165_ = lean_apply_5(v___f_1035_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, lean_box(0));
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; uint8_t v___x_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v___x_1167_ = lean_unbox(v_a_1166_);
lean_dec(v_a_1166_);
if (v___x_1167_ == 0)
{
lean_dec_ref(v_a_1037_);
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_toMonadRef_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
lean_dec_ref(v___x_1024_);
v___y_1149_ = v___y_1040_;
v___y_1150_ = v___y_1041_;
v___y_1151_ = v___y_1042_;
v___y_1152_ = v___y_1043_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_9218__overap_1171_; lean_object* v___x_1172_; 
v___x_1168_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1169_ = l_Lean_indentExpr(v_a_1037_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_9218__overap_1171_ = l_Lean_addTrace___redArg(v___x_1024_, v___x_1032_, v_toMonadRef_1033_, v___x_1034_, v___x_1031_, v___x_1170_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
lean_inc(v___y_1041_);
lean_inc_ref(v___y_1040_);
v___x_1172_ = lean_apply_5(v___x_9218__overap_1171_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, lean_box(0));
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_dec_ref_known(v___x_1172_, 1);
v___y_1149_ = v___y_1040_;
v___y_1150_ = v___y_1041_;
v___y_1151_ = v___y_1042_;
v___y_1152_ = v___y_1043_;
goto v___jp_1148_;
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_a_1037_);
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_toMonadRef_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
lean_dec_ref(v___x_1024_);
v_a_1181_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1165_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1165_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_dec_ref(v_a_1037_);
v___y_1139_ = v___y_1040_;
v___y_1140_ = v___y_1041_;
v___y_1141_ = v___y_1042_;
v___y_1142_ = v___y_1043_;
goto v___jp_1138_;
}
v___jp_1045_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; size_t v_sz_1059_; size_t v___x_1060_; lean_object* v___x_9134__overap_1061_; lean_object* v___x_1062_; 
v___x_1054_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1055_ = lean_mk_array(v___y_1048_, v___x_1054_);
v___x_1056_ = lean_array_get_size(v___y_1047_);
v___x_1057_ = l_Array_toSubarray___redArg(v___y_1047_, v___y_1049_, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1055_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v_sz_1059_ = lean_array_size(v_positions_1023_);
v___x_1060_ = ((size_t)0ULL);
lean_inc_ref(v___x_1024_);
v___x_9134__overap_1061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1024_, v_positions_1023_, v___f_1025_, v_sz_1059_, v___x_1060_, v___x_1058_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
v___x_1062_ = lean_apply_5(v___x_9134__overap_1061_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, lean_box(0));
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v_fst_1064_; size_t v_sz_1065_; lean_object* v___x_9137__overap_1066_; lean_object* v___x_1067_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v_fst_1064_ = lean_ctor_get(v_a_1063_, 0);
lean_inc(v_fst_1064_);
lean_dec(v_a_1063_);
v_sz_1065_ = lean_array_size(v_fst_1064_);
lean_inc_ref(v___x_1024_);
v___x_9137__overap_1066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1024_, v___f_1026_, v_sz_1065_, v___x_1060_, v_fst_1064_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
v___x_1067_ = lean_apply_5(v___x_9137__overap_1066_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, lean_box(0));
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; uint8_t v___x_1069_; lean_object* v___x_9141__overap_1070_; lean_object* v___x_1071_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
v___x_1069_ = 0;
v___x_9141__overap_1070_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1027_, v___x_1024_, v_a_1068_, v___y_1046_, v___x_1069_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
lean_inc(v___y_1051_);
lean_inc_ref(v___y_1050_);
v___x_1071_ = lean_apply_5(v___x_9141__overap_1070_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, lean_box(0));
return v___x_1071_;
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v___y_1046_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___x_1024_);
v_a_1072_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_1067_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1067_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v___y_1046_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___x_1024_);
v_a_1080_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1062_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1062_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
v___jp_1088_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1097_ = l_Array_toSubarray___redArg(v_args_1039_, v_lower_1095_, v_upper_1096_);
v___x_1098_ = l_Subarray_copy___redArg(v___y_1091_);
v___x_1099_ = l_Lean_mkAppN(v_f_1038_, v___x_1098_);
lean_dec_ref(v___x_1098_);
lean_inc_ref(v___x_1099_);
v___x_1100_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1028_, v___x_1099_, v___y_1092_, v___y_1093_, v___y_1090_, v___y_1089_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc_n(v_a_1101_, 2);
lean_dec_ref_known(v___x_1100_, 1);
lean_inc_ref(v___f_1035_);
lean_inc_ref(v___x_1034_);
lean_inc_ref(v_toMonadRef_1033_);
lean_inc_ref(v___x_1032_);
lean_inc(v___x_1031_);
lean_inc_ref(v_positions_1023_);
lean_inc_ref(v___x_1024_);
v___f_1102_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1102_, 0, v___x_1024_);
lean_closure_set(v___f_1102_, 1, v___x_1029_);
lean_closure_set(v___f_1102_, 2, v_positions_1023_);
lean_closure_set(v___f_1102_, 3, v_a_1101_);
lean_closure_set(v___f_1102_, 4, v___x_1099_);
lean_closure_set(v___f_1102_, 5, v___x_1097_);
lean_closure_set(v___f_1102_, 6, v_k_1030_);
lean_closure_set(v___f_1102_, 7, v___x_1031_);
lean_closure_set(v___f_1102_, 8, v___x_1032_);
lean_closure_set(v___f_1102_, 9, v_toMonadRef_1033_);
lean_closure_set(v___f_1102_, 10, v___x_1034_);
lean_closure_set(v___f_1102_, 11, v___f_1035_);
v___x_1103_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1023_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
v___x_1104_ = lean_apply_5(v___f_1035_, v___y_1092_, v___y_1093_, v___y_1090_, v___y_1089_, lean_box(0));
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; uint8_t v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = lean_unbox(v_a_1105_);
lean_dec(v_a_1105_);
if (v___x_1106_ == 0)
{
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_toMonadRef_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
v___y_1046_ = v___f_1102_;
v___y_1047_ = v_a_1101_;
v___y_1048_ = v___x_1103_;
v___y_1049_ = v___y_1094_;
v___y_1050_ = v___y_1092_;
v___y_1051_ = v___y_1093_;
v___y_1052_ = v___y_1090_;
v___y_1053_ = v___y_1089_;
goto v___jp_1045_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_9173__overap_1112_; lean_object* v___x_1113_; 
v___x_1107_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1103_);
v___x_1108_ = l_Nat_reprFast(v___x_1103_);
v___x_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
v___x_1110_ = l_Lean_MessageData_ofFormat(v___x_1109_);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1107_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_inc_ref(v___x_1024_);
v___x_9173__overap_1112_ = l_Lean_addTrace___redArg(v___x_1024_, v___x_1032_, v_toMonadRef_1033_, v___x_1034_, v___x_1031_, v___x_1111_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1090_);
lean_inc(v___y_1093_);
lean_inc_ref(v___y_1092_);
v___x_1113_ = lean_apply_5(v___x_9173__overap_1112_, v___y_1092_, v___y_1093_, v___y_1090_, v___y_1089_, lean_box(0));
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
v___y_1046_ = v___f_1102_;
v___y_1047_ = v_a_1101_;
v___y_1048_ = v___x_1103_;
v___y_1049_ = v___y_1094_;
v___y_1050_ = v___y_1092_;
v___y_1051_ = v___y_1093_;
v___y_1052_ = v___y_1090_;
v___y_1053_ = v___y_1089_;
goto v___jp_1045_;
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_dec(v___x_1103_);
lean_dec_ref(v___f_1102_);
lean_dec(v_a_1101_);
lean_dec(v___y_1094_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_positions_1023_);
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_dec(v___x_1103_);
lean_dec_ref(v___f_1102_);
lean_dec(v_a_1101_);
lean_dec(v___y_1094_);
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_toMonadRef_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_positions_1023_);
v_a_1122_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1104_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1104_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___x_1099_);
lean_dec_ref(v___x_1097_);
lean_dec(v___y_1094_);
lean_dec_ref(v___f_1035_);
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_toMonadRef_1033_);
lean_dec_ref(v___x_1032_);
lean_dec(v___x_1031_);
lean_dec_ref(v_k_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1027_);
lean_dec_ref(v___f_1026_);
lean_dec_ref(v___f_1025_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_positions_1023_);
v_a_1130_ = lean_ctor_get(v___x_1100_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1100_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1100_);
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
v___jp_1138_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1143_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1036_);
lean_inc_ref(v_args_1039_);
v___x_1144_ = l_Array_toSubarray___redArg(v_args_1039_, v___x_1143_, v_numIndParams_1036_);
v___x_1145_ = lean_nat_add(v_numIndParams_1036_, v_numTypeFormers_1028_);
lean_dec(v_numIndParams_1036_);
v___x_1146_ = lean_array_get_size(v_args_1039_);
v___x_1147_ = lean_nat_dec_le(v___x_1145_, v___x_1143_);
if (v___x_1147_ == 0)
{
v___y_1089_ = v___y_1142_;
v___y_1090_ = v___y_1141_;
v___y_1091_ = v___x_1144_;
v___y_1092_ = v___y_1139_;
v___y_1093_ = v___y_1140_;
v___y_1094_ = v___x_1143_;
v_lower_1095_ = v___x_1145_;
v_upper_1096_ = v___x_1146_;
goto v___jp_1088_;
}
else
{
lean_dec(v___x_1145_);
v___y_1089_ = v___y_1142_;
v___y_1090_ = v___y_1141_;
v___y_1091_ = v___x_1144_;
v___y_1092_ = v___y_1139_;
v___y_1093_ = v___y_1140_;
v___y_1094_ = v___x_1143_;
v_lower_1095_ = v___x_1143_;
v_upper_1096_ = v___x_1146_;
goto v___jp_1088_;
}
}
v___jp_1148_:
{
lean_object* v___x_1153_; lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v___x_1153_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1153_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1153_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1189_ = _args[0];
lean_object* v___x_1190_ = _args[1];
lean_object* v___f_1191_ = _args[2];
lean_object* v___f_1192_ = _args[3];
lean_object* v___x_1193_ = _args[4];
lean_object* v_numTypeFormers_1194_ = _args[5];
lean_object* v___x_1195_ = _args[6];
lean_object* v_k_1196_ = _args[7];
lean_object* v___x_1197_ = _args[8];
lean_object* v___x_1198_ = _args[9];
lean_object* v_toMonadRef_1199_ = _args[10];
lean_object* v___x_1200_ = _args[11];
lean_object* v___f_1201_ = _args[12];
lean_object* v_numIndParams_1202_ = _args[13];
lean_object* v_a_1203_ = _args[14];
lean_object* v_f_1204_ = _args[15];
lean_object* v_args_1205_ = _args[16];
lean_object* v___y_1206_ = _args[17];
lean_object* v___y_1207_ = _args[18];
lean_object* v___y_1208_ = _args[19];
lean_object* v___y_1209_ = _args[20];
lean_object* v___y_1210_ = _args[21];
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1189_, v___x_1190_, v___f_1191_, v___f_1192_, v___x_1193_, v_numTypeFormers_1194_, v___x_1195_, v_k_1196_, v___x_1197_, v___x_1198_, v_toMonadRef_1199_, v___x_1200_, v___f_1201_, v_numIndParams_1202_, v_a_1203_, v_f_1204_, v_args_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1211_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1212_; 
v___x_1212_ = l_instMonadEIO___redArg();
return v___x_1212_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1214_ = l_StateRefT_x27_instMonad___redArg(v___x_1213_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1223_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1222_, v___x_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___f_1225_; lean_object* v___x_1226_; 
v___x_1224_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1225_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1226_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1225_, v___x_1224_);
return v___x_1226_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1230_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1231_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1232_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1231_, v___x_1230_, v___x_1229_);
return v___x_1232_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___f_1235_; lean_object* v___x_1236_; 
v___x_1233_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1234_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1235_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1236_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1235_, v___f_1234_, v___x_1233_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1241_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1242_ = l_Lean_Name_append(v___x_1241_, v___x_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1244_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17));
v___x_1245_ = l_Lean_stringToMessageData(v___x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1246_, lean_object* v_numIndParams_1247_, lean_object* v_positions_1248_, lean_object* v_k_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; lean_object* v_toApplicative_1256_; lean_object* v_toFunctor_1257_; lean_object* v_toSeq_1258_; lean_object* v_toSeqLeft_1259_; lean_object* v_toSeqRight_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v_toApplicative_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1400_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1256_ = lean_ctor_get(v___x_1255_, 0);
v_toFunctor_1257_ = lean_ctor_get(v_toApplicative_1256_, 0);
v_toSeq_1258_ = lean_ctor_get(v_toApplicative_1256_, 2);
v_toSeqLeft_1259_ = lean_ctor_get(v_toApplicative_1256_, 3);
v_toSeqRight_1260_ = lean_ctor_get(v_toApplicative_1256_, 4);
v___f_1261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1257_, 2);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toFunctor_1257_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toFunctor_1257_);
v___x_1265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___f_1263_);
lean_ctor_set(v___x_1265_, 1, v___f_1264_);
lean_inc(v_toSeqRight_1260_);
v___f_1266_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1266_, 0, v_toSeqRight_1260_);
lean_inc(v_toSeqLeft_1259_);
v___f_1267_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1267_, 0, v_toSeqLeft_1259_);
lean_inc(v_toSeq_1258_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toSeq_1258_);
v___x_1269_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1265_);
lean_ctor_set(v___x_1269_, 1, v___f_1261_);
lean_ctor_set(v___x_1269_, 2, v___f_1268_);
lean_ctor_set(v___x_1269_, 3, v___f_1267_);
lean_ctor_set(v___x_1269_, 4, v___f_1266_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set(v___x_1270_, 1, v___f_1262_);
v___x_1271_ = l_StateRefT_x27_instMonad___redArg(v___x_1270_);
v_toApplicative_1272_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1271_, 1);
lean_dec(v_unused_1401_);
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1400_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_toApplicative_1272_);
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1400_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_toFunctor_1276_; lean_object* v_toSeq_1277_; lean_object* v_toSeqLeft_1278_; lean_object* v_toSeqRight_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1398_; 
v_toFunctor_1276_ = lean_ctor_get(v_toApplicative_1272_, 0);
v_toSeq_1277_ = lean_ctor_get(v_toApplicative_1272_, 2);
v_toSeqLeft_1278_ = lean_ctor_get(v_toApplicative_1272_, 3);
v_toSeqRight_1279_ = lean_ctor_get(v_toApplicative_1272_, 4);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_toApplicative_1272_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v_toApplicative_1272_, 1);
lean_dec(v_unused_1399_);
v___x_1281_ = v_toApplicative_1272_;
v_isShared_1282_ = v_isSharedCheck_1398_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_toSeqRight_1279_);
lean_inc(v_toSeqLeft_1278_);
lean_inc(v_toSeq_1277_);
lean_inc(v_toFunctor_1276_);
lean_dec(v_toApplicative_1272_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1398_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___f_1283_; lean_object* v___f_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___f_1290_; lean_object* v___x_1292_; 
v___f_1283_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1284_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1276_);
v___f_1285_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1285_, 0, v_toFunctor_1276_);
v___f_1286_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1286_, 0, v_toFunctor_1276_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___f_1285_);
lean_ctor_set(v___x_1287_, 1, v___f_1286_);
v___f_1288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1288_, 0, v_toSeqRight_1279_);
v___f_1289_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1289_, 0, v_toSeqLeft_1278_);
v___f_1290_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1290_, 0, v_toSeq_1277_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 4, v___f_1288_);
lean_ctor_set(v___x_1281_, 3, v___f_1289_);
lean_ctor_set(v___x_1281_, 2, v___f_1290_);
lean_ctor_set(v___x_1281_, 1, v___f_1283_);
lean_ctor_set(v___x_1281_, 0, v___x_1287_);
v___x_1292_ = v___x_1281_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v___f_1283_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v___f_1290_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v___f_1289_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v___f_1288_);
v___x_1292_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v___f_1284_);
lean_ctor_set(v___x_1274_, 0, v___x_1292_);
v___x_1294_ = v___x_1274_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___f_1284_);
v___x_1294_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v_toApplicative_1296_; lean_object* v_toFunctor_1297_; lean_object* v_toSeq_1298_; lean_object* v_toSeqLeft_1299_; lean_object* v_toSeqRight_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v___f_1304_; lean_object* v___f_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v_toMonadRef_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_numTypeFormers_1318_; lean_object* v___x_1319_; 
v___x_1295_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1296_ = lean_ctor_get(v___x_1255_, 0);
v_toFunctor_1297_ = lean_ctor_get(v_toApplicative_1296_, 0);
v_toSeq_1298_ = lean_ctor_get(v_toApplicative_1296_, 2);
v_toSeqLeft_1299_ = lean_ctor_get(v_toApplicative_1296_, 3);
v_toSeqRight_1300_ = lean_ctor_get(v_toApplicative_1296_, 4);
lean_inc_ref_n(v_toFunctor_1297_, 2);
v___f_1301_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1301_, 0, v_toFunctor_1297_);
v___f_1302_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1302_, 0, v_toFunctor_1297_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___f_1301_);
lean_ctor_set(v___x_1303_, 1, v___f_1302_);
lean_inc(v_toSeqRight_1300_);
v___f_1304_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1304_, 0, v_toSeqRight_1300_);
lean_inc(v_toSeqLeft_1299_);
v___f_1305_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1305_, 0, v_toSeqLeft_1299_);
lean_inc(v_toSeq_1298_);
v___f_1306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1306_, 0, v_toSeq_1298_);
v___x_1307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1303_);
lean_ctor_set(v___x_1307_, 1, v___f_1261_);
lean_ctor_set(v___x_1307_, 2, v___f_1306_);
lean_ctor_set(v___x_1307_, 3, v___f_1305_);
lean_ctor_set(v___x_1307_, 4, v___f_1304_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___f_1262_);
v___x_1309_ = l_StateRefT_x27_instMonad___redArg(v___x_1308_);
v___x_1310_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1310_, 0, lean_box(0));
lean_closure_set(v___x_1310_, 1, lean_box(0));
lean_closure_set(v___x_1310_, 2, v___x_1309_);
v___x_1311_ = l_instMonadControlTOfPure___redArg(v___x_1310_);
v___x_1312_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1313_ = lean_ctor_get(v___x_1312_, 0);
v___f_1314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
lean_inc_ref(v___x_1294_);
v___f_1315_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_1315_, 0, v___x_1294_);
v___x_1316_ = l_Lean_instInhabitedExpr;
v___x_1317_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1318_ = lean_array_get_size(v_positions_1248_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
lean_inc(v_a_1251_);
lean_inc_ref(v_a_1250_);
lean_inc_ref(v_below_1246_);
v___x_1319_ = lean_infer_type(v_below_1246_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; lean_object* v___f_1323_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___x_1372_; lean_object* v_a_1373_; uint8_t v___x_1374_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc_n(v_a_1320_, 2);
lean_dec_ref_known(v___x_1319_, 1);
v___x_1321_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1322_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref(v_toMonadRef_1313_);
lean_inc_ref(v___x_1294_);
v___f_1323_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1323_, 0, v_positions_1248_);
lean_closure_set(v___f_1323_, 1, v___x_1294_);
lean_closure_set(v___f_1323_, 2, v___f_1315_);
lean_closure_set(v___f_1323_, 3, v___f_1314_);
lean_closure_set(v___f_1323_, 4, v___x_1311_);
lean_closure_set(v___f_1323_, 5, v_numTypeFormers_1318_);
lean_closure_set(v___f_1323_, 6, v___x_1316_);
lean_closure_set(v___f_1323_, 7, v_k_1249_);
lean_closure_set(v___f_1323_, 8, v___x_1321_);
lean_closure_set(v___f_1323_, 9, v___x_1295_);
lean_closure_set(v___f_1323_, 10, v_toMonadRef_1313_);
lean_closure_set(v___f_1323_, 11, v___x_1317_);
lean_closure_set(v___f_1323_, 12, v___f_1322_);
lean_closure_set(v___f_1323_, 13, v_numIndParams_1247_);
lean_closure_set(v___f_1323_, 14, v_a_1320_);
v___x_1372_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1321_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
if (v___x_1374_ == 0)
{
v___y_1337_ = v_a_1250_;
v___y_1338_ = v_a_1251_;
v___y_1339_ = v_a_1252_;
v___y_1340_ = v_a_1253_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_8829__overap_1378_; lean_object* v___x_1379_; 
v___x_1375_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18);
lean_inc(v_a_1320_);
v___x_1376_ = l_Lean_MessageData_ofExpr(v_a_1320_);
v___x_1377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
lean_inc_ref(v_toMonadRef_1313_);
lean_inc_ref(v___x_1294_);
v___x_8829__overap_1378_ = l_Lean_addTrace___redArg(v___x_1294_, v___x_1295_, v_toMonadRef_1313_, v___x_1317_, v___x_1321_, v___x_1377_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
lean_inc(v_a_1251_);
lean_inc_ref(v_a_1250_);
v___x_1379_ = lean_apply_5(v___x_8829__overap_1378_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, lean_box(0));
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_dec_ref_known(v___x_1379_, 1);
v___y_1337_ = v_a_1250_;
v___y_1338_ = v_a_1251_;
v___y_1339_ = v_a_1252_;
v___y_1340_ = v_a_1253_;
goto v___jp_1336_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref(v___f_1323_);
lean_dec(v_a_1320_);
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_below_1246_);
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
v___jp_1324_:
{
lean_object* v_dummy_1329_; lean_object* v_nargs_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_8825__overap_1334_; lean_object* v___x_1335_; 
v_dummy_1329_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1330_ = l_Lean_Expr_getAppNumArgs(v_a_1320_);
lean_inc(v_nargs_1330_);
v___x_1331_ = lean_mk_array(v_nargs_1330_, v_dummy_1329_);
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1333_ = lean_nat_sub(v_nargs_1330_, v___x_1332_);
lean_dec(v_nargs_1330_);
v___x_8825__overap_1334_ = l_Lean_Expr_withAppAux___redArg(v___f_1323_, v_a_1320_, v___x_1331_, v___x_1333_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
v___x_1335_ = lean_apply_5(v___x_8825__overap_1334_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, lean_box(0));
return v___x_1335_;
}
v___jp_1336_:
{
lean_object* v_toCold_1341_; lean_object* v_options_1342_; uint8_t v_hasTrace_1343_; 
v_toCold_1341_ = lean_ctor_get(v___y_1339_, 0);
v_options_1342_ = lean_ctor_get(v_toCold_1341_, 2);
v_hasTrace_1343_ = lean_ctor_get_uint8(v_options_1342_, sizeof(void*)*1);
if (v_hasTrace_1343_ == 0)
{
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_below_1246_);
v___y_1325_ = v___y_1337_;
v___y_1326_ = v___y_1338_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
goto v___jp_1324_;
}
else
{
lean_object* v_inheritedTraceOptions_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v_inheritedTraceOptions_1344_ = lean_ctor_get(v_toCold_1341_, 11);
v___x_1345_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1346_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1344_, v_options_1342_, v___x_1345_);
if (v___x_1346_ == 0)
{
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_below_1246_);
v___y_1325_ = v___y_1337_;
v___y_1326_ = v___y_1338_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_isTypeCorrect(v_below_1246_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; uint8_t v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = lean_unbox(v_a_1348_);
lean_dec(v_a_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v_a_1351_; uint8_t v___x_1352_; 
v___x_1350_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1321_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = lean_unbox(v_a_1351_);
lean_dec(v_a_1351_);
if (v___x_1352_ == 0)
{
lean_dec_ref(v___x_1294_);
v___y_1325_ = v___y_1337_;
v___y_1326_ = v___y_1338_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_8827__overap_1354_; lean_object* v___x_1355_; 
v___x_1353_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1313_);
v___x_8827__overap_1354_ = l_Lean_addTrace___redArg(v___x_1294_, v___x_1295_, v_toMonadRef_1313_, v___x_1317_, v___x_1321_, v___x_1353_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___x_1355_ = lean_apply_5(v___x_8827__overap_1354_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, lean_box(0));
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_dec_ref_known(v___x_1355_, 1);
v___y_1325_ = v___y_1337_;
v___y_1326_ = v___y_1338_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
goto v___jp_1324_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec_ref(v___f_1323_);
lean_dec(v_a_1320_);
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1294_);
v___y_1325_ = v___y_1337_;
v___y_1326_ = v___y_1338_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
goto v___jp_1324_;
}
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec_ref(v___f_1323_);
lean_dec(v_a_1320_);
lean_dec_ref(v___x_1294_);
v_a_1364_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1347_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1347_);
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
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec_ref(v___f_1315_);
lean_dec_ref(v___x_1311_);
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_k_1249_);
lean_dec_ref(v_positions_1248_);
lean_dec(v_numIndParams_1247_);
lean_dec_ref(v_below_1246_);
v_a_1388_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1319_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1319_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1402_, lean_object* v_numIndParams_1403_, lean_object* v_positions_1404_, lean_object* v_k_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1402_, v_numIndParams_1403_, v_positions_1404_, v_k_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1412_, lean_object* v_inst_1413_, lean_object* v_below_1414_, lean_object* v_numIndParams_1415_, lean_object* v_positions_1416_, lean_object* v_k_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1414_, v_numIndParams_1415_, v_positions_1416_, v_k_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1424_, lean_object* v_inst_1425_, lean_object* v_below_1426_, lean_object* v_numIndParams_1427_, lean_object* v_positions_1428_, lean_object* v_k_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1424_, v_inst_1425_, v_below_1426_, v_numIndParams_1427_, v_positions_1428_, v_k_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1430_);
lean_dec(v_inst_1425_);
return v_res_1435_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1436_ = lean_unsigned_to_nat(32u);
v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1439_ = ((size_t)5ULL);
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = lean_unsigned_to_nat(32u);
v___x_1442_ = lean_mk_empty_array_with_capacity(v___x_1441_);
v___x_1443_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1444_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___x_1442_);
lean_ctor_set(v___x_1444_, 2, v___x_1440_);
lean_ctor_set(v___x_1444_, 3, v___x_1440_);
lean_ctor_set_usize(v___x_1444_, 4, v___x_1439_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; lean_object* v_traceState_1448_; lean_object* v_traces_1449_; lean_object* v___x_1450_; lean_object* v_traceState_1451_; lean_object* v_env_1452_; lean_object* v_nextMacroScope_1453_; lean_object* v_ngen_1454_; lean_object* v_auxDeclNGen_1455_; lean_object* v_cache_1456_; lean_object* v_recordedDeps_1457_; lean_object* v_messages_1458_; lean_object* v_infoState_1459_; lean_object* v_snapshotTasks_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1479_; 
v___x_1447_ = lean_st_ref_get(v___y_1445_);
v_traceState_1448_ = lean_ctor_get(v___x_1447_, 4);
lean_inc_ref(v_traceState_1448_);
lean_dec(v___x_1447_);
v_traces_1449_ = lean_ctor_get(v_traceState_1448_, 0);
lean_inc_ref(v_traces_1449_);
lean_dec_ref(v_traceState_1448_);
v___x_1450_ = lean_st_ref_take(v___y_1445_);
v_traceState_1451_ = lean_ctor_get(v___x_1450_, 4);
v_env_1452_ = lean_ctor_get(v___x_1450_, 0);
v_nextMacroScope_1453_ = lean_ctor_get(v___x_1450_, 1);
v_ngen_1454_ = lean_ctor_get(v___x_1450_, 2);
v_auxDeclNGen_1455_ = lean_ctor_get(v___x_1450_, 3);
v_cache_1456_ = lean_ctor_get(v___x_1450_, 5);
v_recordedDeps_1457_ = lean_ctor_get(v___x_1450_, 6);
v_messages_1458_ = lean_ctor_get(v___x_1450_, 7);
v_infoState_1459_ = lean_ctor_get(v___x_1450_, 8);
v_snapshotTasks_1460_ = lean_ctor_get(v___x_1450_, 9);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1462_ = v___x_1450_;
v_isShared_1463_ = v_isSharedCheck_1479_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_snapshotTasks_1460_);
lean_inc(v_infoState_1459_);
lean_inc(v_messages_1458_);
lean_inc(v_recordedDeps_1457_);
lean_inc(v_cache_1456_);
lean_inc(v_traceState_1451_);
lean_inc(v_auxDeclNGen_1455_);
lean_inc(v_ngen_1454_);
lean_inc(v_nextMacroScope_1453_);
lean_inc(v_env_1452_);
lean_dec(v___x_1450_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1479_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
uint64_t v_tid_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1477_; 
v_tid_1464_ = lean_ctor_get_uint64(v_traceState_1451_, sizeof(void*)*1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_traceState_1451_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v_traceState_1451_, 0);
lean_dec(v_unused_1478_);
v___x_1466_ = v_traceState_1451_;
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_traceState_1451_);
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
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_env_1452_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_nextMacroScope_1453_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_ngen_1454_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_auxDeclNGen_1455_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v_cache_1456_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_recordedDeps_1457_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_messages_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 8, v_infoState_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 9, v_snapshotTasks_1460_);
v___x_1472_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = lean_st_ref_put(v___y_1445_, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_traces_1449_);
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
lean_object* v_toCold_1608_; lean_object* v_currRecDepth_1609_; lean_object* v_ref_1610_; uint16_t v_optionFlags_1611_; uint8_t v_suppressElabErrors_1612_; uint8_t v_isRecordingDeps_1613_; lean_object* v_ref_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v_traceState_1617_; lean_object* v_traces_1618_; lean_object* v___x_1619_; size_t v_sz_1620_; size_t v___x_1621_; lean_object* v___x_1622_; lean_object* v_msg_1623_; lean_object* v___x_1624_; lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1663_; 
v_toCold_1608_ = lean_ctor_get(v___y_1605_, 0);
v_currRecDepth_1609_ = lean_ctor_get(v___y_1605_, 1);
v_ref_1610_ = lean_ctor_get(v___y_1605_, 2);
v_optionFlags_1611_ = lean_ctor_get_uint16(v___y_1605_, sizeof(void*)*3);
v_suppressElabErrors_1612_ = lean_ctor_get_uint8(v___y_1605_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1613_ = lean_ctor_get_uint8(v___y_1605_, sizeof(void*)*3 + 3);
v_ref_1614_ = l_Lean_replaceRef(v_ref_1601_, v_ref_1610_);
lean_inc(v_currRecDepth_1609_);
lean_inc_ref(v_toCold_1608_);
v___x_1615_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1615_, 0, v_toCold_1608_);
lean_ctor_set(v___x_1615_, 1, v_currRecDepth_1609_);
lean_ctor_set(v___x_1615_, 2, v_ref_1614_);
lean_ctor_set_uint16(v___x_1615_, sizeof(void*)*3, v_optionFlags_1611_);
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*3 + 2, v_suppressElabErrors_1612_);
lean_ctor_set_uint8(v___x_1615_, sizeof(void*)*3 + 3, v_isRecordingDeps_1613_);
v___x_1616_ = lean_st_ref_get(v___y_1606_);
v_traceState_1617_ = lean_ctor_get(v___x_1616_, 4);
lean_inc_ref(v_traceState_1617_);
lean_dec(v___x_1616_);
v_traces_1618_ = lean_ctor_get(v_traceState_1617_, 0);
lean_inc_ref(v_traces_1618_);
lean_dec_ref(v_traceState_1617_);
v___x_1619_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1618_);
lean_dec_ref(v_traces_1618_);
v_sz_1620_ = lean_array_size(v___x_1619_);
v___x_1621_ = ((size_t)0ULL);
v___x_1622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1620_, v___x_1621_, v___x_1619_);
v_msg_1623_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1623_, 0, v_data_1600_);
lean_ctor_set(v_msg_1623_, 1, v_msg_1602_);
lean_ctor_set(v_msg_1623_, 2, v___x_1622_);
v___x_1624_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1623_, v___y_1603_, v___y_1604_, v___x_1615_, v___y_1606_);
lean_dec_ref_known(v___x_1615_, 3);
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1627_ = v___x_1624_;
v_isShared_1628_ = v_isSharedCheck_1663_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1663_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v_traceState_1630_; lean_object* v_env_1631_; lean_object* v_nextMacroScope_1632_; lean_object* v_ngen_1633_; lean_object* v_auxDeclNGen_1634_; lean_object* v_cache_1635_; lean_object* v_recordedDeps_1636_; lean_object* v_messages_1637_; lean_object* v_infoState_1638_; lean_object* v_snapshotTasks_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1662_; 
v___x_1629_ = lean_st_ref_take(v___y_1606_);
v_traceState_1630_ = lean_ctor_get(v___x_1629_, 4);
v_env_1631_ = lean_ctor_get(v___x_1629_, 0);
v_nextMacroScope_1632_ = lean_ctor_get(v___x_1629_, 1);
v_ngen_1633_ = lean_ctor_get(v___x_1629_, 2);
v_auxDeclNGen_1634_ = lean_ctor_get(v___x_1629_, 3);
v_cache_1635_ = lean_ctor_get(v___x_1629_, 5);
v_recordedDeps_1636_ = lean_ctor_get(v___x_1629_, 6);
v_messages_1637_ = lean_ctor_get(v___x_1629_, 7);
v_infoState_1638_ = lean_ctor_get(v___x_1629_, 8);
v_snapshotTasks_1639_ = lean_ctor_get(v___x_1629_, 9);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1641_ = v___x_1629_;
v_isShared_1642_ = v_isSharedCheck_1662_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_snapshotTasks_1639_);
lean_inc(v_infoState_1638_);
lean_inc(v_messages_1637_);
lean_inc(v_recordedDeps_1636_);
lean_inc(v_cache_1635_);
lean_inc(v_traceState_1630_);
lean_inc(v_auxDeclNGen_1634_);
lean_inc(v_ngen_1633_);
lean_inc(v_nextMacroScope_1632_);
lean_inc(v_env_1631_);
lean_dec(v___x_1629_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1662_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
uint64_t v_tid_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1660_; 
v_tid_1643_ = lean_ctor_get_uint64(v_traceState_1630_, sizeof(void*)*1);
v_isSharedCheck_1660_ = !lean_is_exclusive(v_traceState_1630_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_traceState_1630_, 0);
lean_dec(v_unused_1661_);
v___x_1645_ = v_traceState_1630_;
v_isShared_1646_ = v_isSharedCheck_1660_;
goto v_resetjp_1644_;
}
else
{
lean_dec(v_traceState_1630_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1660_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_ref_1601_);
lean_ctor_set(v___x_1648_, 1, v_a_1625_);
v___x_1649_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1599_, v___x_1648_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1649_);
v___x_1651_ = v___x_1645_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1649_);
lean_ctor_set_uint64(v_reuseFailAlloc_1659_, sizeof(void*)*1, v_tid_1643_);
v___x_1651_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 4, v___x_1651_);
v___x_1653_ = v___x_1641_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_env_1631_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_nextMacroScope_1632_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_ngen_1633_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_auxDeclNGen_1634_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1658_, 5, v_cache_1635_);
lean_ctor_set(v_reuseFailAlloc_1658_, 6, v_recordedDeps_1636_);
lean_ctor_set(v_reuseFailAlloc_1658_, 7, v_messages_1637_);
lean_ctor_set(v_reuseFailAlloc_1658_, 8, v_infoState_1638_);
lean_ctor_set(v_reuseFailAlloc_1658_, 9, v_snapshotTasks_1639_);
v___x_1653_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_st_ref_put(v___y_1606_, v___x_1653_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 0, v___x_1647_);
v___x_1656_ = v___x_1627_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1647_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1664_, lean_object* v_data_1665_, lean_object* v_ref_1666_, lean_object* v_msg_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1664_, v_data_1665_, v_ref_1666_, v_msg_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1674_, lean_object* v_opt_1675_){
_start:
{
lean_object* v_name_1676_; lean_object* v_defValue_1677_; lean_object* v_map_1678_; lean_object* v___x_1679_; 
v_name_1676_ = lean_ctor_get(v_opt_1675_, 0);
v_defValue_1677_ = lean_ctor_get(v_opt_1675_, 1);
v_map_1678_ = lean_ctor_get(v_opts_1674_, 0);
v___x_1679_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1678_, v_name_1676_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_inc(v_defValue_1677_);
return v_defValue_1677_;
}
else
{
lean_object* v_val_1680_; 
v_val_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_val_1680_);
lean_dec_ref_known(v___x_1679_, 1);
if (lean_obj_tag(v_val_1680_) == 3)
{
lean_object* v_v_1681_; 
v_v_1681_ = lean_ctor_get(v_val_1680_, 0);
lean_inc(v_v_1681_);
lean_dec_ref_known(v_val_1680_, 1);
return v_v_1681_;
}
else
{
lean_dec(v_val_1680_);
lean_inc(v_defValue_1677_);
return v_defValue_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1682_, lean_object* v_opt_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1682_, v_opt_1683_);
lean_dec_ref(v_opt_1683_);
lean_dec_ref(v_opts_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1685_){
_start:
{
if (lean_obj_tag(v_e_1685_) == 0)
{
uint8_t v___x_1686_; 
v___x_1686_ = 2;
return v___x_1686_;
}
else
{
lean_object* v_a_1687_; uint8_t v___x_1688_; 
v_a_1687_ = lean_ctor_get(v_e_1685_, 0);
v___x_1688_ = l_Lean_Expr_hasSyntheticSorry(v_a_1687_);
if (v___x_1688_ == 0)
{
uint8_t v___x_1689_; 
v___x_1689_ = 0;
return v___x_1689_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = 1;
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1691_){
_start:
{
uint8_t v_res_1692_; lean_object* v_r_1693_; 
v_res_1692_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1691_);
lean_dec_ref(v_e_1691_);
v_r_1693_ = lean_box(v_res_1692_);
return v_r_1693_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1694_){
_start:
{
if (lean_obj_tag(v_x_1694_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_a_1696_ = lean_ctor_get(v_x_1694_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v_x_1694_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v_x_1694_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v_x_1694_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 1);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
v_a_1704_ = lean_ctor_get(v_x_1694_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1694_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v_x_1694_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v_x_1694_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 0);
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1712_);
return v_res_1714_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1717_ = l_Lean_stringToMessageData(v___x_1716_);
return v___x_1717_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1718_; double v___x_1719_; 
v___x_1718_ = lean_unsigned_to_nat(1000u);
v___x_1719_ = lean_float_of_nat(v___x_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1720_, uint8_t v_collapsed_1721_, lean_object* v_tag_1722_, lean_object* v_opts_1723_, uint8_t v_clsEnabled_1724_, lean_object* v_oldTraces_1725_, lean_object* v_msg_1726_, lean_object* v_resStartStop_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v_fst_1733_; lean_object* v_snd_1734_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v_data_1738_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; lean_object* v___y_1754_; lean_object* v_a_1755_; uint8_t v___y_1770_; double v___y_1802_; 
v_fst_1733_ = lean_ctor_get(v_resStartStop_1727_, 0);
lean_inc(v_fst_1733_);
v_snd_1734_ = lean_ctor_get(v_resStartStop_1727_, 1);
lean_inc(v_snd_1734_);
lean_dec_ref(v_resStartStop_1727_);
v_fst_1749_ = lean_ctor_get(v_snd_1734_, 0);
lean_inc(v_fst_1749_);
v_snd_1750_ = lean_ctor_get(v_snd_1734_, 1);
lean_inc(v_snd_1750_);
lean_dec(v_snd_1734_);
v___x_1751_ = l_Lean_trace_profiler;
v___x_1752_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1723_, v___x_1751_);
if (v___x_1752_ == 0)
{
v___y_1770_ = v___x_1752_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1808_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1723_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; double v___x_1811_; double v___x_1812_; double v___x_1813_; 
v___x_1809_ = l_Lean_trace_profiler_threshold;
v___x_1810_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1723_, v___x_1809_);
v___x_1811_ = lean_float_of_nat(v___x_1810_);
v___x_1812_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2);
v___x_1813_ = lean_float_div(v___x_1811_, v___x_1812_);
v___y_1802_ = v___x_1813_;
goto v___jp_1801_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; double v___x_1816_; 
v___x_1814_ = l_Lean_trace_profiler_threshold;
v___x_1815_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1723_, v___x_1814_);
v___x_1816_ = lean_float_of_nat(v___x_1815_);
v___y_1802_ = v___x_1816_;
goto v___jp_1801_;
}
}
v___jp_1735_:
{
lean_object* v___x_1739_; 
lean_inc(v___y_1736_);
v___x_1739_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1725_, v_data_1738_, v___y_1736_, v___y_1737_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref_known(v___x_1739_, 1);
v___x_1740_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1733_);
return v___x_1740_;
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_fst_1733_);
v_a_1741_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1739_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1739_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
v___jp_1753_:
{
uint8_t v_result_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; double v___x_1759_; lean_object* v_data_1760_; 
v_result_1756_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1733_);
v___x_1757_ = lean_box(v_result_1756_);
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
v___x_1759_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1722_);
lean_inc_ref(v___x_1758_);
lean_inc(v_cls_1720_);
v_data_1760_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1760_, 0, v_cls_1720_);
lean_ctor_set(v_data_1760_, 1, v___x_1758_);
lean_ctor_set(v_data_1760_, 2, v_tag_1722_);
lean_ctor_set_float(v_data_1760_, sizeof(void*)*3, v___x_1759_);
lean_ctor_set_float(v_data_1760_, sizeof(void*)*3 + 8, v___x_1759_);
lean_ctor_set_uint8(v_data_1760_, sizeof(void*)*3 + 16, v_collapsed_1721_);
if (v___x_1752_ == 0)
{
lean_dec_ref_known(v___x_1758_, 1);
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref(v_tag_1722_);
lean_dec(v_cls_1720_);
v___y_1736_ = v___y_1754_;
v___y_1737_ = v_a_1755_;
v_data_1738_ = v_data_1760_;
goto v___jp_1735_;
}
else
{
lean_object* v_data_1761_; double v___x_1762_; double v___x_1763_; 
lean_dec_ref_known(v_data_1760_, 3);
v_data_1761_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1761_, 0, v_cls_1720_);
lean_ctor_set(v_data_1761_, 1, v___x_1758_);
lean_ctor_set(v_data_1761_, 2, v_tag_1722_);
v___x_1762_ = lean_unbox_float(v_fst_1749_);
lean_dec(v_fst_1749_);
lean_ctor_set_float(v_data_1761_, sizeof(void*)*3, v___x_1762_);
v___x_1763_ = lean_unbox_float(v_snd_1750_);
lean_dec(v_snd_1750_);
lean_ctor_set_float(v_data_1761_, sizeof(void*)*3 + 8, v___x_1763_);
lean_ctor_set_uint8(v_data_1761_, sizeof(void*)*3 + 16, v_collapsed_1721_);
v___y_1736_ = v___y_1754_;
v___y_1737_ = v_a_1755_;
v_data_1738_ = v_data_1761_;
goto v___jp_1735_;
}
}
v___jp_1764_:
{
lean_object* v_ref_1765_; lean_object* v___x_1766_; 
v_ref_1765_ = lean_ctor_get(v___y_1730_, 2);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v___y_1729_);
lean_inc_ref(v___y_1728_);
lean_inc(v_fst_1733_);
v___x_1766_ = lean_apply_6(v_msg_1726_, v_fst_1733_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, lean_box(0));
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___y_1754_ = v_ref_1765_;
v_a_1755_ = v_a_1767_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1768_; 
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1754_ = v_ref_1765_;
v_a_1755_ = v___x_1768_;
goto v___jp_1753_;
}
}
v___jp_1769_:
{
if (v_clsEnabled_1724_ == 0)
{
if (v___y_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v_traceState_1772_; lean_object* v_env_1773_; lean_object* v_nextMacroScope_1774_; lean_object* v_ngen_1775_; lean_object* v_auxDeclNGen_1776_; lean_object* v_cache_1777_; lean_object* v_recordedDeps_1778_; lean_object* v_messages_1779_; lean_object* v_infoState_1780_; lean_object* v_snapshotTasks_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_snd_1750_);
lean_dec(v_fst_1749_);
lean_dec_ref(v_msg_1726_);
lean_dec_ref(v_tag_1722_);
lean_dec(v_cls_1720_);
v___x_1771_ = lean_st_ref_take(v___y_1731_);
v_traceState_1772_ = lean_ctor_get(v___x_1771_, 4);
v_env_1773_ = lean_ctor_get(v___x_1771_, 0);
v_nextMacroScope_1774_ = lean_ctor_get(v___x_1771_, 1);
v_ngen_1775_ = lean_ctor_get(v___x_1771_, 2);
v_auxDeclNGen_1776_ = lean_ctor_get(v___x_1771_, 3);
v_cache_1777_ = lean_ctor_get(v___x_1771_, 5);
v_recordedDeps_1778_ = lean_ctor_get(v___x_1771_, 6);
v_messages_1779_ = lean_ctor_get(v___x_1771_, 7);
v_infoState_1780_ = lean_ctor_get(v___x_1771_, 8);
v_snapshotTasks_1781_ = lean_ctor_get(v___x_1771_, 9);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1783_ = v___x_1771_;
v_isShared_1784_ = v_isSharedCheck_1800_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_snapshotTasks_1781_);
lean_inc(v_infoState_1780_);
lean_inc(v_messages_1779_);
lean_inc(v_recordedDeps_1778_);
lean_inc(v_cache_1777_);
lean_inc(v_traceState_1772_);
lean_inc(v_auxDeclNGen_1776_);
lean_inc(v_ngen_1775_);
lean_inc(v_nextMacroScope_1774_);
lean_inc(v_env_1773_);
lean_dec(v___x_1771_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1800_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
uint64_t v_tid_1785_; lean_object* v_traces_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1799_; 
v_tid_1785_ = lean_ctor_get_uint64(v_traceState_1772_, sizeof(void*)*1);
v_traces_1786_ = lean_ctor_get(v_traceState_1772_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_traceState_1772_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1788_ = v_traceState_1772_;
v_isShared_1789_ = v_isSharedCheck_1799_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_traces_1786_);
lean_dec(v_traceState_1772_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1799_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1790_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1725_, v_traces_1786_);
lean_dec_ref(v_traces_1786_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1790_);
v___x_1792_ = v___x_1788_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1790_);
lean_ctor_set_uint64(v_reuseFailAlloc_1798_, sizeof(void*)*1, v_tid_1785_);
v___x_1792_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1794_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 4, v___x_1792_);
v___x_1794_ = v___x_1783_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_env_1773_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_nextMacroScope_1774_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_ngen_1775_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_auxDeclNGen_1776_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1797_, 5, v_cache_1777_);
lean_ctor_set(v_reuseFailAlloc_1797_, 6, v_recordedDeps_1778_);
lean_ctor_set(v_reuseFailAlloc_1797_, 7, v_messages_1779_);
lean_ctor_set(v_reuseFailAlloc_1797_, 8, v_infoState_1780_);
lean_ctor_set(v_reuseFailAlloc_1797_, 9, v_snapshotTasks_1781_);
v___x_1794_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_st_ref_put(v___y_1731_, v___x_1794_);
v___x_1796_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1733_);
return v___x_1796_;
}
}
}
}
}
else
{
goto v___jp_1764_;
}
}
else
{
goto v___jp_1764_;
}
}
v___jp_1801_:
{
double v___x_1803_; double v___x_1804_; double v___x_1805_; uint8_t v___x_1806_; 
v___x_1803_ = lean_unbox_float(v_snd_1750_);
v___x_1804_ = lean_unbox_float(v_fst_1749_);
v___x_1805_ = lean_float_sub(v___x_1803_, v___x_1804_);
v___x_1806_ = lean_float_decLt(v___y_1802_, v___x_1805_);
v___y_1770_ = v___x_1806_;
goto v___jp_1769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1817_, lean_object* v_collapsed_1818_, lean_object* v_tag_1819_, lean_object* v_opts_1820_, lean_object* v_clsEnabled_1821_, lean_object* v_oldTraces_1822_, lean_object* v_msg_1823_, lean_object* v_resStartStop_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v_collapsed_boxed_1830_; uint8_t v_clsEnabled_boxed_1831_; lean_object* v_res_1832_; 
v_collapsed_boxed_1830_ = lean_unbox(v_collapsed_1818_);
v_clsEnabled_boxed_1831_ = lean_unbox(v_clsEnabled_1821_);
v_res_1832_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1817_, v_collapsed_boxed_1830_, v_tag_1819_, v_opts_1820_, v_clsEnabled_boxed_1831_, v_oldTraces_1822_, v_msg_1823_, v_resStartStop_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec_ref(v_opts_1820_);
return v_res_1832_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1833_; double v___x_1834_; 
v___x_1833_ = lean_unsigned_to_nat(1000000000u);
v___x_1834_ = lean_float_of_nat(v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1835_, lean_object* v_numIndParams_1836_, lean_object* v_positions_1837_, lean_object* v_fnIndex_1838_, lean_object* v_recArg_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_toCold_1845_; lean_object* v_options_1846_; lean_object* v_inheritedTraceOptions_1847_; uint8_t v_hasTrace_1848_; lean_object* v___x_1849_; lean_object* v___f_1850_; 
v_toCold_1845_ = lean_ctor_get(v_a_1842_, 0);
v_options_1846_ = lean_ctor_get(v_toCold_1845_, 2);
v_inheritedTraceOptions_1847_ = lean_ctor_get(v_toCold_1845_, 11);
v_hasTrace_1848_ = lean_ctor_get_uint8(v_options_1846_, sizeof(void*)*1);
v___x_1849_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1835_);
lean_inc_ref(v_recArg_1839_);
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1850_, 0, v___x_1849_);
lean_closure_set(v___f_1850_, 1, v_fnIndex_1838_);
lean_closure_set(v___f_1850_, 2, v_recArg_1839_);
lean_closure_set(v___f_1850_, 3, v_below_1835_);
if (v_hasTrace_1848_ == 0)
{
lean_object* v___x_1851_; 
lean_dec_ref(v_recArg_1839_);
v___x_1851_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1835_, v_numIndParams_1836_, v_positions_1837_, v___f_1850_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1851_;
}
else
{
lean_object* v___f_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v_a_1860_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v_a_1875_; 
lean_inc_ref(v_below_1835_);
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1852_, 0, v_below_1835_);
lean_closure_set(v___f_1852_, 1, v_recArg_1839_);
v___x_1853_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1854_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1855_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1847_, v_options_1846_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1925_ = l_Lean_trace_profiler;
v___x_1926_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1846_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_object* v___x_1927_; 
lean_dec_ref(v___f_1852_);
v___x_1927_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1835_, v_numIndParams_1836_, v_positions_1837_, v___f_1850_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1927_;
}
else
{
goto v___jp_1884_;
}
}
else
{
goto v___jp_1884_;
}
v___jp_1857_:
{
lean_object* v___x_1861_; double v___x_1862_; double v___x_1863_; double v___x_1864_; double v___x_1865_; double v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1861_ = lean_io_mono_nanos_now();
v___x_1862_ = lean_float_of_nat(v___y_1859_);
v___x_1863_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1864_ = lean_float_div(v___x_1862_, v___x_1863_);
v___x_1865_ = lean_float_of_nat(v___x_1861_);
v___x_1866_ = lean_float_div(v___x_1865_, v___x_1863_);
v___x_1867_ = lean_box_float(v___x_1864_);
v___x_1868_ = lean_box_float(v___x_1866_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_a_1860_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1853_, v_hasTrace_1848_, v___x_1854_, v_options_1846_, v___x_1856_, v___y_1858_, v___f_1852_, v___x_1870_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1871_;
}
v___jp_1872_:
{
lean_object* v___x_1876_; double v___x_1877_; double v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1876_ = lean_io_get_num_heartbeats();
v___x_1877_ = lean_float_of_nat(v___y_1874_);
v___x_1878_ = lean_float_of_nat(v___x_1876_);
v___x_1879_ = lean_box_float(v___x_1877_);
v___x_1880_ = lean_box_float(v___x_1878_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_a_1875_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1853_, v_hasTrace_1848_, v___x_1854_, v_options_1846_, v___x_1856_, v___y_1873_, v___f_1852_, v___x_1882_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
return v___x_1883_;
}
v___jp_1884_:
{
lean_object* v___x_1885_; lean_object* v_a_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1885_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1843_);
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
v___x_1887_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1888_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1846_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_io_mono_nanos_now();
v___x_1890_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1835_, v_numIndParams_1836_, v_positions_1837_, v___f_1850_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 1);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
v___y_1858_ = v_a_1886_;
v___y_1859_ = v___x_1889_;
v_a_1860_ = v___x_1896_;
goto v___jp_1857_;
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
v_a_1899_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1890_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1890_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 0);
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
v___y_1858_ = v_a_1886_;
v___y_1859_ = v___x_1889_;
v_a_1860_ = v___x_1904_;
goto v___jp_1857_;
}
}
}
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_io_get_num_heartbeats();
v___x_1908_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1835_, v_numIndParams_1836_, v_positions_1837_, v___f_1850_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set_tag(v___x_1911_, 1);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
v___y_1873_ = v_a_1886_;
v___y_1874_ = v___x_1907_;
v_a_1875_ = v___x_1914_;
goto v___jp_1872_;
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
v_a_1917_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1908_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1908_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
lean_ctor_set_tag(v___x_1919_, 0);
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
v___y_1873_ = v_a_1886_;
v___y_1874_ = v___x_1907_;
v_a_1875_ = v___x_1922_;
goto v___jp_1872_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1928_, lean_object* v_numIndParams_1929_, lean_object* v_positions_1930_, lean_object* v_fnIndex_1931_, lean_object* v_recArg_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_Elab_Structural_toBelow(v_below_1928_, v_numIndParams_1929_, v_positions_1930_, v_fnIndex_1931_, v_recArg_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1939_, lean_object* v_x_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1940_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1947_, lean_object* v_x_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1947_, v_x_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1955_, lean_object* v___y_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc(v___y_1956_);
v___x_1963_ = lean_apply_7(v_k_1955_, v_b_1957_, v___y_1956_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, lean_box(0));
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_1964_, lean_object* v___y_1965_, lean_object* v_b_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1964_, v___y_1965_, v_b_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1965_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_1973_, uint8_t v_bi_1974_, lean_object* v_type_1975_, lean_object* v_k_1976_, uint8_t v_kind_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___f_1984_; lean_object* v___x_1985_; 
lean_inc(v___y_1978_);
v___f_1984_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1984_, 0, v_k_1976_);
lean_closure_set(v___f_1984_, 1, v___y_1978_);
v___x_1985_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1973_, v_bi_1974_, v_type_1975_, v___f_1984_, v_kind_1977_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
if (lean_obj_tag(v___x_1985_) == 0)
{
return v___x_1985_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1985_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_1994_, lean_object* v_bi_1995_, lean_object* v_type_1996_, lean_object* v_k_1997_, lean_object* v_kind_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v_bi_boxed_2005_; uint8_t v_kind_boxed_2006_; lean_object* v_res_2007_; 
v_bi_boxed_2005_ = lean_unbox(v_bi_1995_);
v_kind_boxed_2006_ = lean_unbox(v_kind_1998_);
v_res_2007_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_1994_, v_bi_boxed_2005_, v_type_1996_, v_k_1997_, v_kind_boxed_2006_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2008_, lean_object* v_name_2009_, uint8_t v_bi_2010_, lean_object* v_type_2011_, lean_object* v_k_2012_, uint8_t v_kind_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v___x_2020_; 
v___x_2020_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2009_, v_bi_2010_, v_type_2011_, v_k_2012_, v_kind_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2021_, lean_object* v_name_2022_, lean_object* v_bi_2023_, lean_object* v_type_2024_, lean_object* v_k_2025_, lean_object* v_kind_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
uint8_t v_bi_boxed_2033_; uint8_t v_kind_boxed_2034_; lean_object* v_res_2035_; 
v_bi_boxed_2033_ = lean_unbox(v_bi_2023_);
v_kind_boxed_2034_ = lean_unbox(v_kind_2026_);
v_res_2035_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2021_, v_name_2022_, v_bi_boxed_2033_, v_type_2024_, v_k_2025_, v_kind_boxed_2034_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2036_, lean_object* v___y_2037_, lean_object* v_b_2038_, lean_object* v_c_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; 
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2037_);
v___x_2045_ = lean_apply_8(v_k_2036_, v_b_2038_, v_c_2039_, v___y_2037_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, lean_box(0));
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2046_, lean_object* v___y_2047_, lean_object* v_b_2048_, lean_object* v_c_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2046_, v___y_2047_, v_b_2048_, v_c_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2047_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2056_, lean_object* v_maxFVars_2057_, lean_object* v_k_2058_, uint8_t v_cleanupAnnotations_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___f_2066_; uint8_t v___x_2067_; uint8_t v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
lean_inc(v___y_2060_);
v___f_2066_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2066_, 0, v_k_2058_);
lean_closure_set(v___f_2066_, 1, v___y_2060_);
v___x_2067_ = 1;
v___x_2068_ = 0;
v___x_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2069_, 0, v_maxFVars_2057_);
v___x_2070_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2056_, v___x_2067_, v___x_2068_, v___x_2067_, v___x_2068_, v___x_2069_, v___f_2066_, v_cleanupAnnotations_2059_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec_ref_known(v___x_2069_, 1);
if (lean_obj_tag(v___x_2070_) == 0)
{
return v___x_2070_;
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2079_, lean_object* v_maxFVars_2080_, lean_object* v_k_2081_, lean_object* v_cleanupAnnotations_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2089_; lean_object* v_res_2090_; 
v_cleanupAnnotations_boxed_2089_ = lean_unbox(v_cleanupAnnotations_2082_);
v_res_2090_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2079_, v_maxFVars_2080_, v_k_2081_, v_cleanupAnnotations_boxed_2089_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2091_, lean_object* v_e_2092_, lean_object* v_maxFVars_2093_, lean_object* v_k_2094_, uint8_t v_cleanupAnnotations_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2092_, v_maxFVars_2093_, v_k_2094_, v_cleanupAnnotations_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2103_, lean_object* v_e_2104_, lean_object* v_maxFVars_2105_, lean_object* v_k_2106_, lean_object* v_cleanupAnnotations_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2114_; lean_object* v_res_2115_; 
v_cleanupAnnotations_boxed_2114_ = lean_unbox(v_cleanupAnnotations_2107_);
v_res_2115_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2103_, v_e_2104_, v_maxFVars_2105_, v_k_2106_, v_cleanupAnnotations_boxed_2114_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2116_, lean_object* v_msg_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_ref_2123_; lean_object* v___x_2124_; lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2170_; 
v_ref_2123_ = lean_ctor_get(v___y_2120_, 2);
v___x_2124_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2170_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2170_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; lean_object* v_traceState_2130_; lean_object* v_env_2131_; lean_object* v_nextMacroScope_2132_; lean_object* v_ngen_2133_; lean_object* v_auxDeclNGen_2134_; lean_object* v_cache_2135_; lean_object* v_recordedDeps_2136_; lean_object* v_messages_2137_; lean_object* v_infoState_2138_; lean_object* v_snapshotTasks_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2169_; 
v___x_2129_ = lean_st_ref_take(v___y_2121_);
v_traceState_2130_ = lean_ctor_get(v___x_2129_, 4);
v_env_2131_ = lean_ctor_get(v___x_2129_, 0);
v_nextMacroScope_2132_ = lean_ctor_get(v___x_2129_, 1);
v_ngen_2133_ = lean_ctor_get(v___x_2129_, 2);
v_auxDeclNGen_2134_ = lean_ctor_get(v___x_2129_, 3);
v_cache_2135_ = lean_ctor_get(v___x_2129_, 5);
v_recordedDeps_2136_ = lean_ctor_get(v___x_2129_, 6);
v_messages_2137_ = lean_ctor_get(v___x_2129_, 7);
v_infoState_2138_ = lean_ctor_get(v___x_2129_, 8);
v_snapshotTasks_2139_ = lean_ctor_get(v___x_2129_, 9);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2141_ = v___x_2129_;
v_isShared_2142_ = v_isSharedCheck_2169_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_snapshotTasks_2139_);
lean_inc(v_infoState_2138_);
lean_inc(v_messages_2137_);
lean_inc(v_recordedDeps_2136_);
lean_inc(v_cache_2135_);
lean_inc(v_traceState_2130_);
lean_inc(v_auxDeclNGen_2134_);
lean_inc(v_ngen_2133_);
lean_inc(v_nextMacroScope_2132_);
lean_inc(v_env_2131_);
lean_dec(v___x_2129_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2169_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
uint64_t v_tid_2143_; lean_object* v_traces_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2168_; 
v_tid_2143_ = lean_ctor_get_uint64(v_traceState_2130_, sizeof(void*)*1);
v_traces_2144_ = lean_ctor_get(v_traceState_2130_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_traceState_2130_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2146_ = v_traceState_2130_;
v_isShared_2147_ = v_isSharedCheck_2168_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_traces_2144_);
lean_dec(v_traceState_2130_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2168_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; double v___x_2150_; uint8_t v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2151_ = 0;
v___x_2152_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2153_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2153_, 0, v_cls_2116_);
lean_ctor_set(v___x_2153_, 1, v___x_2149_);
lean_ctor_set(v___x_2153_, 2, v___x_2152_);
lean_ctor_set_float(v___x_2153_, sizeof(void*)*3, v___x_2150_);
lean_ctor_set_float(v___x_2153_, sizeof(void*)*3 + 8, v___x_2150_);
lean_ctor_set_uint8(v___x_2153_, sizeof(void*)*3 + 16, v___x_2151_);
v___x_2154_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2155_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v_a_2125_);
lean_ctor_set(v___x_2155_, 2, v___x_2154_);
lean_inc(v_ref_2123_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v_ref_2123_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = l_Lean_PersistentArray_push___redArg(v_traces_2144_, v___x_2156_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2157_);
v___x_2159_ = v___x_2146_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2157_);
lean_ctor_set_uint64(v_reuseFailAlloc_2167_, sizeof(void*)*1, v_tid_2143_);
v___x_2159_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2161_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v___x_2159_);
v___x_2161_ = v___x_2141_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_env_2131_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_nextMacroScope_2132_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_ngen_2133_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_auxDeclNGen_2134_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2166_, 5, v_cache_2135_);
lean_ctor_set(v_reuseFailAlloc_2166_, 6, v_recordedDeps_2136_);
lean_ctor_set(v_reuseFailAlloc_2166_, 7, v_messages_2137_);
lean_ctor_set(v_reuseFailAlloc_2166_, 8, v_infoState_2138_);
lean_ctor_set(v_reuseFailAlloc_2166_, 9, v_snapshotTasks_2139_);
v___x_2161_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = lean_st_ref_put(v___y_2121_, v___x_2161_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2148_);
v___x_2164_ = v___x_2127_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2148_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2171_, lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2171_, v_msg_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
return v_res_2178_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2179_, lean_object* v_as_2180_, size_t v_i_2181_, size_t v_stop_2182_){
_start:
{
uint8_t v___x_2187_; 
v___x_2187_ = lean_usize_dec_eq(v_i_2181_, v_stop_2182_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v_fnName_2189_; lean_object* v_recArgPos_2190_; uint8_t v___x_2191_; 
v___x_2188_ = lean_array_uget_borrowed(v_as_2180_, v_i_2181_);
v_fnName_2189_ = lean_ctor_get(v___x_2188_, 0);
v_recArgPos_2190_ = lean_ctor_get(v___x_2188_, 2);
lean_inc(v_recArgPos_2190_);
lean_inc(v_fnName_2189_);
v___x_2191_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2189_, v_recArgPos_2190_, v_e_2179_);
if (v___x_2191_ == 0)
{
goto v___jp_2183_;
}
else
{
if (v___x_2191_ == 0)
{
goto v___jp_2183_;
}
else
{
return v___x_2191_;
}
}
}
else
{
uint8_t v___x_2192_; 
v___x_2192_ = 0;
return v___x_2192_;
}
v___jp_2183_:
{
size_t v___x_2184_; size_t v___x_2185_; 
v___x_2184_ = ((size_t)1ULL);
v___x_2185_ = lean_usize_add(v_i_2181_, v___x_2184_);
v_i_2181_ = v___x_2185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2193_, lean_object* v_as_2194_, lean_object* v_i_2195_, lean_object* v_stop_2196_){
_start:
{
size_t v_i_boxed_2197_; size_t v_stop_boxed_2198_; uint8_t v_res_2199_; lean_object* v_r_2200_; 
v_i_boxed_2197_ = lean_unbox_usize(v_i_2195_);
lean_dec(v_i_2195_);
v_stop_boxed_2198_ = lean_unbox_usize(v_stop_2196_);
lean_dec(v_stop_2196_);
v_res_2199_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2193_, v_as_2194_, v_i_boxed_2197_, v_stop_boxed_2198_);
lean_dec_ref(v_as_2194_);
lean_dec_ref(v_e_2193_);
v_r_2200_ = lean_box(v_res_2199_);
return v_r_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2201_, lean_object* v_____do__lift_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_toCold_2209_; lean_object* v_options_2210_; uint8_t v_hasTrace_2211_; 
v_toCold_2209_ = lean_ctor_get(v___y_2206_, 0);
v_options_2210_ = lean_ctor_get(v_toCold_2209_, 2);
v_hasTrace_2211_ = lean_ctor_get_uint8(v_options_2210_, sizeof(void*)*1);
if (v_hasTrace_2211_ == 0)
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v___x_2201_);
v___x_2212_ = lean_box(v_hasTrace_2211_);
v___x_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2214_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2215_ = l_Lean_Name_append(v___x_2214_, v___x_2201_);
v___x_2216_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2202_, v_options_2210_, v___x_2215_);
lean_dec(v___x_2215_);
v___x_2217_ = lean_box(v___x_2216_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2217_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2219_, lean_object* v_____do__lift_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2219_, v_____do__lift_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v_____do__lift_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v___x_2231_; lean_object* v_env_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2231_ = lean_st_ref_get(v___y_2229_);
v_env_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc_ref(v_env_2232_);
lean_dec(v___x_2231_);
v___x_2233_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2232_, v_declName_2228_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2235_, v___y_2236_);
lean_dec(v___y_2236_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v_toApplicative_2247_; lean_object* v_toFunctor_2248_; lean_object* v_toSeq_2249_; lean_object* v_toSeqLeft_2250_; lean_object* v_toSeqRight_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___f_2254_; lean_object* v___f_2255_; lean_object* v___x_2256_; lean_object* v___f_2257_; lean_object* v___f_2258_; lean_object* v___f_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v_toApplicative_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2295_; 
v___x_2246_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2247_ = lean_ctor_get(v___x_2246_, 0);
v_toFunctor_2248_ = lean_ctor_get(v_toApplicative_2247_, 0);
v_toSeq_2249_ = lean_ctor_get(v_toApplicative_2247_, 2);
v_toSeqLeft_2250_ = lean_ctor_get(v_toApplicative_2247_, 3);
v_toSeqRight_2251_ = lean_ctor_get(v_toApplicative_2247_, 4);
v___f_2252_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2253_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2248_, 2);
v___f_2254_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2254_, 0, v_toFunctor_2248_);
v___f_2255_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2255_, 0, v_toFunctor_2248_);
v___x_2256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___f_2254_);
lean_ctor_set(v___x_2256_, 1, v___f_2255_);
lean_inc(v_toSeqRight_2251_);
v___f_2257_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2257_, 0, v_toSeqRight_2251_);
lean_inc(v_toSeqLeft_2250_);
v___f_2258_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2258_, 0, v_toSeqLeft_2250_);
lean_inc(v_toSeq_2249_);
v___f_2259_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2259_, 0, v_toSeq_2249_);
v___x_2260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2256_);
lean_ctor_set(v___x_2260_, 1, v___f_2252_);
lean_ctor_set(v___x_2260_, 2, v___f_2259_);
lean_ctor_set(v___x_2260_, 3, v___f_2258_);
lean_ctor_set(v___x_2260_, 4, v___f_2257_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v___f_2253_);
v___x_2262_ = l_StateRefT_x27_instMonad___redArg(v___x_2261_);
v_toApplicative_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v___x_2262_, 1);
lean_dec(v_unused_2296_);
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2295_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_toApplicative_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2295_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_toFunctor_2267_; lean_object* v_toSeq_2268_; lean_object* v_toSeqLeft_2269_; lean_object* v_toSeqRight_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2293_; 
v_toFunctor_2267_ = lean_ctor_get(v_toApplicative_2263_, 0);
v_toSeq_2268_ = lean_ctor_get(v_toApplicative_2263_, 2);
v_toSeqLeft_2269_ = lean_ctor_get(v_toApplicative_2263_, 3);
v_toSeqRight_2270_ = lean_ctor_get(v_toApplicative_2263_, 4);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_toApplicative_2263_);
if (v_isSharedCheck_2293_ == 0)
{
lean_object* v_unused_2294_; 
v_unused_2294_ = lean_ctor_get(v_toApplicative_2263_, 1);
lean_dec(v_unused_2294_);
v___x_2272_ = v_toApplicative_2263_;
v_isShared_2273_ = v_isSharedCheck_2293_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_toSeqRight_2270_);
lean_inc(v_toSeqLeft_2269_);
lean_inc(v_toSeq_2268_);
lean_inc(v_toFunctor_2267_);
lean_dec(v_toApplicative_2263_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2293_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___f_2274_; lean_object* v___f_2275_; lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___f_2280_; lean_object* v___f_2281_; lean_object* v___x_2283_; 
v___f_2274_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2275_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2267_);
v___f_2276_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2276_, 0, v_toFunctor_2267_);
v___f_2277_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2277_, 0, v_toFunctor_2267_);
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___f_2276_);
lean_ctor_set(v___x_2278_, 1, v___f_2277_);
v___f_2279_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2279_, 0, v_toSeqRight_2270_);
v___f_2280_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2280_, 0, v_toSeqLeft_2269_);
v___f_2281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2281_, 0, v_toSeq_2268_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 4, v___f_2279_);
lean_ctor_set(v___x_2272_, 3, v___f_2280_);
lean_ctor_set(v___x_2272_, 2, v___f_2281_);
lean_ctor_set(v___x_2272_, 1, v___f_2274_);
lean_ctor_set(v___x_2272_, 0, v___x_2278_);
v___x_2283_ = v___x_2272_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2278_);
lean_ctor_set(v_reuseFailAlloc_2292_, 1, v___f_2274_);
lean_ctor_set(v_reuseFailAlloc_2292_, 2, v___f_2281_);
lean_ctor_set(v_reuseFailAlloc_2292_, 3, v___f_2280_);
lean_ctor_set(v_reuseFailAlloc_2292_, 4, v___f_2279_);
v___x_2283_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2285_; 
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v___f_2275_);
lean_ctor_set(v___x_2265_, 0, v___x_2283_);
v___x_2285_ = v___x_2265_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v___f_2275_);
v___x_2285_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_23553__overap_2289_; lean_object* v___x_2290_; 
v___x_2286_ = l_StateRefT_x27_instMonad___redArg(v___x_2285_);
v___x_2287_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2288_ = l_instInhabitedOfMonad___redArg(v___x_2286_, v___x_2287_);
v___x_23553__overap_2289_ = lean_panic_fn_borrowed(v___x_2288_, v_msg_2239_);
lean_dec(v___x_2288_);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
v___x_2290_ = lean_apply_6(v___x_23553__overap_2289_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, lean_box(0));
return v___x_2290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
return v_res_2304_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
lean_ctor_set(v___x_2310_, 2, v___x_2309_);
lean_ctor_set(v___x_2310_, 3, v___x_2309_);
lean_ctor_set(v___x_2310_, 4, v___x_2308_);
lean_ctor_set(v___x_2310_, 5, v___x_2308_);
lean_ctor_set(v___x_2310_, 6, v___x_2308_);
lean_ctor_set(v___x_2310_, 7, v___x_2308_);
lean_ctor_set(v___x_2310_, 8, v___x_2308_);
lean_ctor_set(v___x_2310_, 9, v___x_2308_);
lean_ctor_set(v___x_2310_, 10, v___x_2308_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = lean_unsigned_to_nat(32u);
v___x_2312_ = lean_mk_empty_array_with_capacity(v___x_2311_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2314_ = ((size_t)5ULL);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_unsigned_to_nat(32u);
v___x_2317_ = lean_mk_empty_array_with_capacity(v___x_2316_);
v___x_2318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2319_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v___x_2317_);
lean_ctor_set(v___x_2319_, 2, v___x_2315_);
lean_ctor_set(v___x_2319_, 3, v___x_2315_);
lean_ctor_set_usize(v___x_2319_, 4, v___x_2314_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2320_ = lean_box(1);
v___x_2321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v___x_2321_);
lean_ctor_set(v___x_2323_, 2, v___x_2320_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2326_ = l_Lean_stringToMessageData(v___x_2325_);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2329_ = l_Lean_stringToMessageData(v___x_2328_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2332_ = l_Lean_stringToMessageData(v___x_2331_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2338_ = l_Lean_stringToMessageData(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2345_, lean_object* v_declHint_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_env_2351_; uint8_t v___x_2352_; 
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_st_ref_get(v___y_2347_);
v_env_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc_ref(v_env_2351_);
lean_dec(v___x_2350_);
v___x_2352_ = l_Lean_Name_isAnonymous(v_declHint_2346_);
if (v___x_2352_ == 0)
{
uint8_t v_isExporting_2353_; 
v_isExporting_2353_ = lean_ctor_get_uint8(v_env_2351_, sizeof(void*)*8);
if (v_isExporting_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec_ref(v_env_2351_);
lean_dec(v_declHint_2346_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_msg_2345_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
lean_inc_ref(v_env_2351_);
v___x_2355_ = l_Lean_Environment_setExporting(v_env_2351_, v___x_2352_);
lean_inc(v_declHint_2346_);
lean_inc_ref(v___x_2355_);
v___x_2356_ = l_Lean_Environment_contains(v___x_2355_, v_declHint_2346_, v_isExporting_2353_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; 
lean_dec_ref(v___x_2355_);
lean_dec_ref(v_env_2351_);
lean_dec(v_declHint_2346_);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_msg_2345_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_c_2363_; lean_object* v___x_2364_; 
v___x_2358_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2360_ = l_Lean_Options_empty;
v___x_2361_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2355_);
lean_ctor_set(v___x_2361_, 1, v___x_2358_);
lean_ctor_set(v___x_2361_, 2, v___x_2359_);
lean_ctor_set(v___x_2361_, 3, v___x_2360_);
lean_inc(v_declHint_2346_);
v___x_2362_ = l_Lean_MessageData_ofConstName(v_declHint_2346_, v___x_2352_);
v_c_2363_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2363_, 0, v___x_2361_);
lean_ctor_set(v_c_2363_, 1, v___x_2362_);
v___x_2364_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2351_, v_declHint_2346_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
lean_dec_ref(v_env_2351_);
lean_dec(v_declHint_2346_);
v___x_2365_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v_c_2363_);
v___x_2367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = l_Lean_MessageData_note(v___x_2368_);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_msg_2345_);
lean_ctor_set(v___x_2370_, 1, v___x_2369_);
v___x_2371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
return v___x_2371_;
}
else
{
lean_object* v_val_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2406_; 
v_val_2372_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2374_ = v___x_2364_;
v_isShared_2375_ = v_isSharedCheck_2406_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_val_2372_);
lean_dec(v___x_2364_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2406_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_mod_2378_; uint8_t v___x_2379_; 
v___x_2376_ = l_Lean_Environment_header(v_env_2351_);
lean_dec_ref(v_env_2351_);
v___x_2377_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2376_);
v_mod_2378_ = lean_array_get(v___x_2349_, v___x_2377_, v_val_2372_);
lean_dec(v_val_2372_);
lean_dec_ref(v___x_2377_);
v___x_2379_ = l_Lean_isPrivateName(v_declHint_2346_);
lean_dec(v_declHint_2346_);
if (v___x_2379_ == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v_c_2363_);
v___x_2382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_MessageData_ofName(v_mod_2378_);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = l_Lean_MessageData_note(v___x_2387_);
v___x_2389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_msg_2345_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2389_);
v___x_2391_ = v___x_2374_;
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
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2393_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v_c_2363_);
v___x_2395_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2394_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v___x_2397_ = l_Lean_MessageData_ofName(v_mod_2378_);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2396_);
lean_ctor_set(v___x_2398_, 1, v___x_2397_);
v___x_2399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_MessageData_note(v___x_2400_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v_msg_2345_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2402_);
v___x_2404_ = v___x_2374_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2407_; 
lean_dec_ref(v_env_2351_);
lean_dec(v_declHint_2346_);
v___x_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2407_, 0, v_msg_2345_);
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2408_, lean_object* v_declHint_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2408_, v_declHint_2409_, v___y_2410_);
lean_dec(v___y_2410_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2413_, lean_object* v_declHint_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2431_; 
v___x_2421_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2413_, v_declHint_2414_, v___y_2419_);
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2431_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2431_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2426_ = l_Lean_unknownIdentifierMessageTag;
v___x_2427_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v_a_2422_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2427_);
v___x_2429_ = v___x_2424_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2432_, lean_object* v_declHint_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2432_, v_declHint_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_ref_2447_; lean_object* v___x_2448_; lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2457_; 
v_ref_2447_ = lean_ctor_get(v___y_2444_, 2);
v___x_2448_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2457_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_inc(v_ref_2447_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_ref_2447_);
lean_ctor_set(v___x_2453_, 1, v_a_2449_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set_tag(v___x_2451_, 1);
lean_ctor_set(v___x_2451_, 0, v___x_2453_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2465_, lean_object* v_msg_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_toCold_2473_; lean_object* v_currRecDepth_2474_; lean_object* v_ref_2475_; uint16_t v_optionFlags_2476_; uint8_t v_suppressElabErrors_2477_; uint8_t v_isRecordingDeps_2478_; lean_object* v_ref_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v_toCold_2473_ = lean_ctor_get(v___y_2470_, 0);
v_currRecDepth_2474_ = lean_ctor_get(v___y_2470_, 1);
v_ref_2475_ = lean_ctor_get(v___y_2470_, 2);
v_optionFlags_2476_ = lean_ctor_get_uint16(v___y_2470_, sizeof(void*)*3);
v_suppressElabErrors_2477_ = lean_ctor_get_uint8(v___y_2470_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2478_ = lean_ctor_get_uint8(v___y_2470_, sizeof(void*)*3 + 3);
v_ref_2479_ = l_Lean_replaceRef(v_ref_2465_, v_ref_2475_);
lean_inc(v_currRecDepth_2474_);
lean_inc_ref(v_toCold_2473_);
v___x_2480_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2480_, 0, v_toCold_2473_);
lean_ctor_set(v___x_2480_, 1, v_currRecDepth_2474_);
lean_ctor_set(v___x_2480_, 2, v_ref_2479_);
lean_ctor_set_uint16(v___x_2480_, sizeof(void*)*3, v_optionFlags_2476_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*3 + 2, v_suppressElabErrors_2477_);
lean_ctor_set_uint8(v___x_2480_, sizeof(void*)*3 + 3, v_isRecordingDeps_2478_);
v___x_2481_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2466_, v___y_2468_, v___y_2469_, v___x_2480_, v___y_2471_);
lean_dec_ref_known(v___x_2480_, 3);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2482_, lean_object* v_msg_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2482_, v_msg_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec(v_ref_2482_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2491_, lean_object* v_msg_2492_, lean_object* v_declHint_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; lean_object* v_a_2501_; lean_object* v___x_2502_; 
v___x_2500_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2492_, v_declHint_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2491_, v_a_2501_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2503_, lean_object* v_msg_2504_, lean_object* v_declHint_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2503_, v_msg_2504_, v_declHint_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v_ref_2503_);
return v_res_2512_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2515_ = l_Lean_stringToMessageData(v___x_2514_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2518_ = l_Lean_stringToMessageData(v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2519_, lean_object* v_constName_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2527_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2528_ = 0;
lean_inc(v_constName_2520_);
v___x_2529_ = l_Lean_MessageData_ofConstName(v_constName_2520_, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2527_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
v___x_2531_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2530_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2519_, v___x_2532_, v_constName_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2534_, lean_object* v_constName_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2534_, v_constName_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec(v_ref_2534_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_ref_2550_; lean_object* v___x_2551_; 
v_ref_2550_ = lean_ctor_get(v___y_2547_, 2);
v___x_2551_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2550_, v_constName_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
lean_dec(v___y_2557_);
lean_dec_ref(v___y_2556_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; lean_object* v_env_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; 
v___x_2567_ = lean_st_ref_get(v___y_2565_);
v_env_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref(v_env_2568_);
lean_dec(v___x_2567_);
v___x_2569_ = 0;
lean_inc(v_constName_2560_);
v___x_2570_ = l_Lean_Environment_find_x3f(v_env_2568_, v_constName_2560_, v___x_2569_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2571_;
}
else
{
lean_object* v_val_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec(v_constName_2560_);
v_val_2572_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2570_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_val_2572_);
lean_dec(v___x_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 0);
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_val_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
return v_res_2587_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2592_ = lean_unsigned_to_nat(53u);
v___x_2593_ = lean_unsigned_to_nat(62u);
v___x_2594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2596_ = l_mkPanicMessageWithDecl(v___x_2595_, v___x_2594_, v___x_2593_, v___x_2592_, v___x_2591_);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2597_, size_t v_i_2598_, lean_object* v_bs_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
uint8_t v___x_2606_; 
v___x_2606_ = lean_usize_dec_lt(v_i_2598_, v_sz_2597_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_bs_2599_);
return v___x_2607_;
}
else
{
lean_object* v_v_2608_; lean_object* v___x_2609_; lean_object* v_bs_x27_2610_; lean_object* v_a_2612_; lean_object* v___x_2617_; 
v_v_2608_ = lean_array_uget(v_bs_2599_, v_i_2598_);
v___x_2609_ = lean_unsigned_to_nat(0u);
v_bs_x27_2610_ = lean_array_uset(v_bs_2599_, v_i_2598_, v___x_2609_);
v___x_2617_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2608_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v___x_2617_, 1);
if (lean_obj_tag(v_a_2618_) == 6)
{
lean_object* v_val_2619_; lean_object* v_numFields_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; 
v_val_2619_ = lean_ctor_get(v_a_2618_, 0);
lean_inc_ref(v_val_2619_);
lean_dec_ref_known(v_a_2618_, 1);
v_numFields_2620_ = lean_ctor_get(v_val_2619_, 4);
lean_inc(v_numFields_2620_);
lean_dec_ref(v_val_2619_);
v___x_2621_ = 0;
v___x_2622_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2622_, 0, v_numFields_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2609_);
lean_ctor_set_uint8(v___x_2622_, sizeof(void*)*2, v___x_2621_);
v_a_2612_ = v___x_2622_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec(v_a_2618_);
v___x_2623_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2624_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2623_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v_a_2612_ = v_a_2625_;
goto v___jp_2611_;
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref(v_bs_x27_2610_);
v_a_2626_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2624_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2624_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec_ref(v_bs_x27_2610_);
v_a_2634_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2617_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2617_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
v___jp_2611_:
{
size_t v___x_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = ((size_t)1ULL);
v___x_2614_ = lean_usize_add(v_i_2598_, v___x_2613_);
v___x_2615_ = lean_array_uset(v_bs_x27_2610_, v_i_2598_, v_a_2612_);
v_i_2598_ = v___x_2614_;
v_bs_2599_ = v___x_2615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2642_, lean_object* v_i_2643_, lean_object* v_bs_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
size_t v_sz_boxed_2651_; size_t v_i_boxed_2652_; lean_object* v_res_2653_; 
v_sz_boxed_2651_ = lean_unbox_usize(v_sz_2642_);
lean_dec(v_sz_2642_);
v_i_boxed_2652_ = lean_unbox_usize(v_i_2643_);
lean_dec(v_i_2643_);
v_res_2653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2651_, v_i_boxed_2652_, v_bs_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
return v_res_2653_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_unsigned_to_nat(16u);
v___x_2656_ = lean_mk_array(v___x_2655_, v___x_2654_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2658_ = lean_unsigned_to_nat(0u);
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___x_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2662_, uint8_t v_alsoCasesOn_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v___x_2673_; 
v___x_2673_ = l_Lean_Expr_isApp(v_e_2662_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref(v_e_2662_);
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_Expr_getAppFn(v_e_2662_);
if (lean_obj_tag(v___x_2676_) == 4)
{
lean_object* v_declName_2677_; lean_object* v_us_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2833_; 
v_declName_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc_n(v_declName_2677_, 2);
v_us_2678_ = lean_ctor_get(v___x_2676_, 1);
lean_inc(v_us_2678_);
lean_dec_ref_known(v___x_2676_, 2);
v___x_2679_ = l_Lean_instInhabitedExpr;
v___x_2680_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2677_, v___y_2668_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2683_ = v___x_2680_;
v_isShared_2684_ = v_isSharedCheck_2833_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2680_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2833_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
if (lean_obj_tag(v_a_2681_) == 1)
{
lean_object* v_val_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2726_; 
v_val_2685_ = lean_ctor_get(v_a_2681_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_a_2681_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2687_ = v_a_2681_;
v_isShared_2688_ = v_isSharedCheck_2726_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_val_2685_);
lean_dec(v_a_2681_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2726_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_dummy_2689_; lean_object* v_nargs_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v_args_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_dummy_2689_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2690_ = l_Lean_Expr_getAppNumArgs(v_e_2662_);
lean_inc(v_nargs_2690_);
v___x_2691_ = lean_mk_array(v_nargs_2690_, v_dummy_2689_);
v___x_2692_ = lean_unsigned_to_nat(1u);
v___x_2693_ = lean_nat_sub(v_nargs_2690_, v___x_2692_);
lean_dec(v_nargs_2690_);
v_args_2694_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2662_, v___x_2691_, v___x_2693_);
v___x_2695_ = lean_array_get_size(v_args_2694_);
v___x_2696_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2685_);
v___x_2697_ = lean_nat_dec_lt(v___x_2695_, v___x_2696_);
lean_dec(v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v_numParams_2698_; lean_object* v_numDiscrs_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v_numParams_2698_ = lean_ctor_get(v_val_2685_, 0);
v_numDiscrs_2699_ = lean_ctor_get(v_val_2685_, 1);
v___x_2700_ = lean_array_mk(v_us_2678_);
v___x_2701_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2698_);
v___x_2702_ = l_Array_extract___redArg(v_args_2694_, v___x_2701_, v_numParams_2698_);
v___x_2703_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2685_);
v___x_2704_ = lean_array_get(v___x_2679_, v_args_2694_, v___x_2703_);
lean_dec(v___x_2703_);
v___x_2705_ = lean_nat_add(v_numParams_2698_, v___x_2692_);
v___x_2706_ = lean_nat_add(v___x_2705_, v_numDiscrs_2699_);
lean_inc(v___x_2706_);
lean_inc_ref_n(v_args_2694_, 2);
v___x_2707_ = l_Array_toSubarray___redArg(v_args_2694_, v___x_2705_, v___x_2706_);
v___x_2708_ = l_Subarray_copy___redArg(v___x_2707_);
v___x_2709_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2685_);
v___x_2710_ = lean_nat_add(v___x_2706_, v___x_2709_);
lean_dec(v___x_2709_);
lean_inc(v___x_2710_);
v___x_2711_ = l_Array_toSubarray___redArg(v_args_2694_, v___x_2706_, v___x_2710_);
v___x_2712_ = l_Subarray_copy___redArg(v___x_2711_);
v___x_2713_ = l_Array_toSubarray___redArg(v_args_2694_, v___x_2710_, v___x_2695_);
v___x_2714_ = l_Subarray_copy___redArg(v___x_2713_);
v___x_2715_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2715_, 0, v_val_2685_);
lean_ctor_set(v___x_2715_, 1, v_declName_2677_);
lean_ctor_set(v___x_2715_, 2, v___x_2700_);
lean_ctor_set(v___x_2715_, 3, v___x_2702_);
lean_ctor_set(v___x_2715_, 4, v___x_2704_);
lean_ctor_set(v___x_2715_, 5, v___x_2708_);
lean_ctor_set(v___x_2715_, 6, v___x_2712_);
lean_ctor_set(v___x_2715_, 7, v___x_2714_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2715_);
v___x_2717_ = v___x_2687_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2719_; 
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2717_);
v___x_2719_ = v___x_2683_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
lean_dec_ref(v_args_2694_);
lean_del_object(v___x_2687_);
lean_dec(v_val_2685_);
lean_dec(v_us_2678_);
lean_dec(v_declName_2677_);
v___x_2722_ = lean_box(0);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 0, v___x_2722_);
v___x_2724_ = v___x_2683_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
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
else
{
lean_object* v___x_2727_; 
lean_del_object(v___x_2683_);
lean_dec(v_a_2681_);
v___x_2727_ = lean_st_ref_get(v___y_2668_);
if (v_alsoCasesOn_2663_ == 0)
{
lean_dec(v___x_2727_);
lean_dec(v_us_2678_);
lean_dec(v_declName_2677_);
lean_dec_ref(v_e_2662_);
goto v___jp_2670_;
}
else
{
lean_object* v_env_2728_; uint8_t v___x_2729_; 
v_env_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc_ref(v_env_2728_);
lean_dec(v___x_2727_);
lean_inc(v_declName_2677_);
v___x_2729_ = l_Lean_isCasesOnRecursor(v_env_2728_, v_declName_2677_);
if (v___x_2729_ == 0)
{
lean_dec(v_us_2678_);
lean_dec(v_declName_2677_);
lean_dec_ref(v_e_2662_);
goto v___jp_2670_;
}
else
{
lean_object* v_indName_2730_; lean_object* v___x_2731_; 
v_indName_2730_ = l_Lean_Name_getPrefix(v_declName_2677_);
v___x_2731_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2730_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2824_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2824_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2824_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
if (lean_obj_tag(v_a_2732_) == 5)
{
lean_object* v_val_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2819_; 
v_val_2736_ = lean_ctor_get(v_a_2732_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_a_2732_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2738_ = v_a_2732_;
v_isShared_2739_ = v_isSharedCheck_2819_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_val_2736_);
lean_dec(v_a_2732_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2819_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v_toConstantVal_2740_; lean_object* v_numParams_2741_; lean_object* v_numIndices_2742_; lean_object* v_ctors_2743_; lean_object* v_nargs_2744_; lean_object* v_dummy_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v_args_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v_toConstantVal_2740_ = lean_ctor_get(v_val_2736_, 0);
lean_inc_ref(v_toConstantVal_2740_);
v_numParams_2741_ = lean_ctor_get(v_val_2736_, 1);
lean_inc(v_numParams_2741_);
v_numIndices_2742_ = lean_ctor_get(v_val_2736_, 2);
lean_inc(v_numIndices_2742_);
v_ctors_2743_ = lean_ctor_get(v_val_2736_, 4);
lean_inc(v_ctors_2743_);
v_nargs_2744_ = l_Lean_Expr_getAppNumArgs(v_e_2662_);
v_dummy_2745_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2744_);
v___x_2746_ = lean_mk_array(v_nargs_2744_, v_dummy_2745_);
v___x_2747_ = lean_unsigned_to_nat(1u);
v___x_2748_ = lean_nat_sub(v_nargs_2744_, v___x_2747_);
lean_dec(v_nargs_2744_);
v_args_2749_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2662_, v___x_2746_, v___x_2748_);
v___x_2750_ = lean_nat_add(v_numParams_2741_, v___x_2747_);
v___x_2751_ = lean_nat_add(v___x_2750_, v_numIndices_2742_);
v___x_2752_ = lean_nat_add(v___x_2751_, v___x_2747_);
lean_dec(v___x_2751_);
v___x_2753_ = l_Lean_InductiveVal_numCtors(v_val_2736_);
lean_dec_ref(v_val_2736_);
v___x_2754_ = lean_nat_add(v___x_2752_, v___x_2753_);
lean_dec(v___x_2753_);
v___x_2755_ = lean_array_get_size(v_args_2749_);
v___x_2756_ = lean_nat_dec_le(v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
lean_dec(v___x_2754_);
lean_dec(v___x_2752_);
lean_dec(v___x_2750_);
lean_dec_ref(v_args_2749_);
lean_dec(v_ctors_2743_);
lean_dec(v_numIndices_2742_);
lean_dec(v_numParams_2741_);
lean_dec_ref(v_toConstantVal_2740_);
lean_del_object(v___x_2738_);
lean_dec(v_us_2678_);
lean_dec(v_declName_2677_);
v___x_2757_ = lean_box(0);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2757_);
v___x_2759_ = v___x_2734_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
else
{
lean_object* v___x_2761_; lean_object* v_params_2762_; lean_object* v_motive_2763_; lean_object* v_discrs_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v_discrInfos_2767_; lean_object* v_alts_2768_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v_lower_2810_; lean_object* v_upper_2811_; uint8_t v___x_2818_; 
lean_del_object(v___x_2734_);
v___x_2761_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2741_);
lean_inc_ref_n(v_args_2749_, 3);
v_params_2762_ = l_Array_toSubarray___redArg(v_args_2749_, v___x_2761_, v_numParams_2741_);
v_motive_2763_ = lean_array_get(v___x_2679_, v_args_2749_, v_numParams_2741_);
lean_dec(v_numParams_2741_);
lean_inc(v___x_2752_);
v_discrs_2764_ = l_Array_toSubarray___redArg(v_args_2749_, v___x_2750_, v___x_2752_);
v___x_2765_ = lean_nat_add(v_numIndices_2742_, v___x_2747_);
lean_dec(v_numIndices_2742_);
v___x_2766_ = lean_box(0);
v_discrInfos_2767_ = lean_mk_array(v___x_2765_, v___x_2766_);
lean_inc(v___x_2754_);
v_alts_2768_ = l_Array_toSubarray___redArg(v_args_2749_, v___x_2752_, v___x_2754_);
v___x_2818_ = lean_nat_dec_le(v___x_2754_, v___x_2761_);
if (v___x_2818_ == 0)
{
v_lower_2810_ = v___x_2754_;
v_upper_2811_ = v___x_2755_;
goto v___jp_2809_;
}
else
{
lean_dec(v___x_2754_);
v_lower_2810_ = v___x_2761_;
v_upper_2811_ = v___x_2755_;
goto v___jp_2809_;
}
v___jp_2769_:
{
lean_object* v___x_2772_; size_t v_sz_2773_; size_t v___x_2774_; lean_object* v___x_2775_; 
v___x_2772_ = lean_array_mk(v_ctors_2743_);
v_sz_2773_ = lean_array_size(v___x_2772_);
v___x_2774_ = ((size_t)0ULL);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2773_, v___x_2774_, v___x_2772_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2800_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_2800_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2800_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v_start_2780_; lean_object* v_stop_2781_; lean_object* v_start_2782_; lean_object* v_stop_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v_start_2780_ = lean_ctor_get(v_params_2762_, 1);
lean_inc(v_start_2780_);
v_stop_2781_ = lean_ctor_get(v_params_2762_, 2);
lean_inc(v_stop_2781_);
v_start_2782_ = lean_ctor_get(v_discrs_2764_, 1);
lean_inc(v_start_2782_);
v_stop_2783_ = lean_ctor_get(v_discrs_2764_, 2);
lean_inc(v_stop_2783_);
v___x_2784_ = lean_nat_sub(v_stop_2781_, v_start_2780_);
lean_dec(v_start_2780_);
lean_dec(v_stop_2781_);
v___x_2785_ = lean_nat_sub(v_stop_2783_, v_start_2782_);
lean_dec(v_start_2782_);
lean_dec(v_stop_2783_);
v___x_2786_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2787_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2784_);
lean_ctor_set(v___x_2787_, 1, v___x_2785_);
lean_ctor_set(v___x_2787_, 2, v_a_2776_);
lean_ctor_set(v___x_2787_, 3, v___y_2771_);
lean_ctor_set(v___x_2787_, 4, v_discrInfos_2767_);
lean_ctor_set(v___x_2787_, 5, v___x_2786_);
v___x_2788_ = lean_array_mk(v_us_2678_);
v___x_2789_ = l_Subarray_copy___redArg(v_params_2762_);
v___x_2790_ = l_Subarray_copy___redArg(v_discrs_2764_);
v___x_2791_ = l_Subarray_copy___redArg(v_alts_2768_);
v___x_2792_ = l_Subarray_copy___redArg(v___y_2770_);
v___x_2793_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2787_);
lean_ctor_set(v___x_2793_, 1, v_declName_2677_);
lean_ctor_set(v___x_2793_, 2, v___x_2788_);
lean_ctor_set(v___x_2793_, 3, v___x_2789_);
lean_ctor_set(v___x_2793_, 4, v_motive_2763_);
lean_ctor_set(v___x_2793_, 5, v___x_2790_);
lean_ctor_set(v___x_2793_, 6, v___x_2791_);
lean_ctor_set(v___x_2793_, 7, v___x_2792_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 1);
lean_ctor_set(v___x_2738_, 0, v___x_2793_);
v___x_2795_ = v___x_2738_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2795_);
v___x_2797_ = v___x_2778_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec_ref(v_alts_2768_);
lean_dec_ref(v_discrInfos_2767_);
lean_dec_ref(v_discrs_2764_);
lean_dec(v_motive_2763_);
lean_dec_ref(v_params_2762_);
lean_del_object(v___x_2738_);
lean_dec(v_us_2678_);
lean_dec(v_declName_2677_);
v_a_2801_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2775_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2775_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
v___jp_2809_:
{
lean_object* v_levelParams_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_levelParams_2812_ = lean_ctor_get(v_toConstantVal_2740_, 1);
lean_inc(v_levelParams_2812_);
lean_dec_ref(v_toConstantVal_2740_);
v___x_2813_ = l_Array_toSubarray___redArg(v_args_2749_, v_lower_2810_, v_upper_2811_);
v___x_2814_ = l_List_lengthTR___redArg(v_levelParams_2812_);
lean_dec(v_levelParams_2812_);
v___x_2815_ = l_List_lengthTR___redArg(v_us_2678_);
v___x_2816_ = lean_nat_dec_eq(v___x_2814_, v___x_2815_);
lean_dec(v___x_2815_);
lean_dec(v___x_2814_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
v___x_2817_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2770_ = v___x_2813_;
v___y_2771_ = v___x_2817_;
goto v___jp_2769_;
}
else
{
v___y_2770_ = v___x_2813_;
v___y_2771_ = v___x_2766_;
goto v___jp_2769_;
}
}
}
}
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2822_; 
lean_dec(v_a_2732_);
lean_dec(v_us_2678_);
lean_dec(v_declName_2677_);
lean_dec_ref(v_e_2662_);
v___x_2820_ = lean_box(0);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 0, v___x_2820_);
v___x_2822_ = v___x_2734_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v___x_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_us_2678_);
lean_dec(v_declName_2677_);
lean_dec_ref(v_e_2662_);
v_a_2825_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2731_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2731_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
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
lean_dec_ref(v___x_2676_);
lean_dec_ref(v_e_2662_);
goto v___jp_2670_;
}
}
v___jp_2670_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_box(0);
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2834_, lean_object* v_alsoCasesOn_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2842_; lean_object* v_res_2843_; 
v_alsoCasesOn_boxed_2842_ = lean_unbox(v_alsoCasesOn_2835_);
v_res_2843_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2834_, v_alsoCasesOn_boxed_2842_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
if (lean_obj_tag(v_a_2844_) == 0)
{
lean_object* v___x_2846_; 
v___x_2846_ = l_List_reverse___redArg(v_a_2845_);
return v___x_2846_;
}
else
{
lean_object* v_head_2847_; lean_object* v_tail_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2857_; 
v_head_2847_ = lean_ctor_get(v_a_2844_, 0);
v_tail_2848_ = lean_ctor_get(v_a_2844_, 1);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_a_2844_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2850_ = v_a_2844_;
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_tail_2848_);
lean_inc(v_head_2847_);
lean_dec(v_a_2844_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2852_ = l_Lean_MessageData_ofExpr(v_head_2847_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 1, v_a_2845_);
lean_ctor_set(v___x_2850_, 0, v___x_2852_);
v___x_2854_ = v___x_2850_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_a_2845_);
v___x_2854_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
v_a_2844_ = v_tail_2848_;
v_a_2845_ = v___x_2854_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2858_, lean_object* v_x_2859_){
_start:
{
lean_object* v_fnName_2860_; uint8_t v___x_2861_; 
v_fnName_2860_ = lean_ctor_get(v_x_2859_, 0);
v___x_2861_ = l_Lean_Expr_isConstOf(v_x_2858_, v_fnName_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2862_, lean_object* v_x_2863_){
_start:
{
uint8_t v_res_2864_; lean_object* v_r_2865_; 
v_res_2864_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2862_, v_x_2863_);
lean_dec_ref(v_x_2863_);
lean_dec_ref(v_x_2862_);
v_r_2865_ = lean_box(v_res_2864_);
return v_r_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2866_, lean_object* v_type_2867_, lean_object* v_val_2868_, lean_object* v_k_2869_, uint8_t v_nondep_2870_, uint8_t v_kind_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___f_2878_; lean_object* v___x_2879_; 
lean_inc(v___y_2872_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2878_, 0, v_k_2869_);
lean_closure_set(v___f_2878_, 1, v___y_2872_);
v___x_2879_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2866_, v_type_2867_, v_val_2868_, v___f_2878_, v_nondep_2870_, v_kind_2871_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
if (lean_obj_tag(v___x_2879_) == 0)
{
return v___x_2879_;
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2888_, lean_object* v_type_2889_, lean_object* v_val_2890_, lean_object* v_k_2891_, lean_object* v_nondep_2892_, lean_object* v_kind_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
uint8_t v_nondep_boxed_2900_; uint8_t v_kind_boxed_2901_; lean_object* v_res_2902_; 
v_nondep_boxed_2900_ = lean_unbox(v_nondep_2892_);
v_kind_boxed_2901_ = lean_unbox(v_kind_2893_);
v_res_2902_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2888_, v_type_2889_, v_val_2890_, v_k_2891_, v_nondep_boxed_2900_, v_kind_boxed_2901_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2903_, uint8_t v_usedLetOnly_2904_, lean_object* v_x_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
lean_object* v___x_2912_; 
lean_inc(v___y_2910_);
lean_inc_ref(v___y_2909_);
lean_inc(v___y_2908_);
lean_inc_ref(v___y_2907_);
lean_inc(v___y_2906_);
lean_inc_ref(v_x_2905_);
v___x_2912_ = lean_apply_7(v_k_2903_, v_x_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, lean_box(0));
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; uint8_t v___x_2917_; uint8_t v___x_2918_; lean_object* v___x_2919_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v___x_2914_ = lean_unsigned_to_nat(1u);
v___x_2915_ = lean_mk_empty_array_with_capacity(v___x_2914_);
v___x_2916_ = lean_array_push(v___x_2915_, v_x_2905_);
v___x_2917_ = 0;
v___x_2918_ = 1;
v___x_2919_ = l_Lean_Meta_mkLetFVars(v___x_2916_, v_a_2913_, v_usedLetOnly_2904_, v___x_2917_, v___x_2918_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec_ref(v___x_2916_);
return v___x_2919_;
}
else
{
lean_dec_ref(v_x_2905_);
return v___x_2912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2920_, lean_object* v_usedLetOnly_2921_, lean_object* v_x_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
uint8_t v_usedLetOnly_boxed_2929_; lean_object* v_res_2930_; 
v_usedLetOnly_boxed_2929_ = lean_unbox(v_usedLetOnly_2921_);
v_res_2930_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2920_, v_usedLetOnly_boxed_2929_, v_x_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2931_, lean_object* v_type_2932_, lean_object* v_val_2933_, lean_object* v_k_2934_, uint8_t v_nondep_2935_, uint8_t v_kind_2936_, uint8_t v_usedLetOnly_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; 
v___x_2944_ = lean_box(v_usedLetOnly_2937_);
v___f_2945_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2945_, 0, v_k_2934_);
lean_closure_set(v___f_2945_, 1, v___x_2944_);
v___x_2946_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2931_, v_type_2932_, v_val_2933_, v___f_2945_, v_nondep_2935_, v_kind_2936_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2947_, lean_object* v_type_2948_, lean_object* v_val_2949_, lean_object* v_k_2950_, lean_object* v_nondep_2951_, lean_object* v_kind_2952_, lean_object* v_usedLetOnly_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
uint8_t v_nondep_boxed_2960_; uint8_t v_kind_boxed_2961_; uint8_t v_usedLetOnly_boxed_2962_; lean_object* v_res_2963_; 
v_nondep_boxed_2960_ = lean_unbox(v_nondep_2951_);
v_kind_boxed_2961_ = lean_unbox(v_kind_2952_);
v_usedLetOnly_boxed_2962_ = lean_unbox(v_usedLetOnly_2953_);
v_res_2963_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2947_, v_type_2948_, v_val_2949_, v_k_2950_, v_nondep_boxed_2960_, v_kind_boxed_2961_, v_usedLetOnly_boxed_2962_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_2964_, lean_object* v_positions_2965_, lean_object* v_recFnNames_2966_, lean_object* v_containsRecFn_2967_, lean_object* v_below_2968_, size_t v_sz_2969_, size_t v_i_2970_, lean_object* v_bs_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
uint8_t v___x_2978_; 
v___x_2978_ = lean_usize_dec_lt(v_i_2970_, v_sz_2969_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; 
lean_dec_ref(v_below_2968_);
lean_dec_ref(v_containsRecFn_2967_);
lean_dec_ref(v_recFnNames_2966_);
lean_dec_ref(v_positions_2965_);
lean_dec_ref(v_recArgInfos_2964_);
v___x_2979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_bs_2971_);
return v___x_2979_;
}
else
{
lean_object* v_v_2980_; lean_object* v___x_2981_; lean_object* v_bs_x27_2982_; lean_object* v___x_2983_; 
v_v_2980_ = lean_array_uget(v_bs_2971_, v_i_2970_);
v___x_2981_ = lean_unsigned_to_nat(0u);
v_bs_x27_2982_ = lean_array_uset(v_bs_2971_, v_i_2970_, v___x_2981_);
lean_inc_ref(v___y_2975_);
lean_inc_ref(v_below_2968_);
lean_inc_ref(v_containsRecFn_2967_);
lean_inc_ref(v_recFnNames_2966_);
lean_inc_ref(v_positions_2965_);
lean_inc_ref(v_recArgInfos_2964_);
v___x_2983_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2964_, v_positions_2965_, v_recFnNames_2966_, v_containsRecFn_2967_, v_below_2968_, v_v_2980_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; size_t v___x_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = ((size_t)1ULL);
v___x_2986_ = lean_usize_add(v_i_2970_, v___x_2985_);
v___x_2987_ = lean_array_uset(v_bs_x27_2982_, v_i_2970_, v_a_2984_);
v_i_2970_ = v___x_2986_;
v_bs_2971_ = v___x_2987_;
goto _start;
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref(v_bs_x27_2982_);
lean_dec_ref(v_below_2968_);
lean_dec_ref(v_containsRecFn_2967_);
lean_dec_ref(v_recFnNames_2966_);
lean_dec_ref(v_positions_2965_);
lean_dec_ref(v_recArgInfos_2964_);
v_a_2989_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2983_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2983_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_2999_ = l_Lean_stringToMessageData(v___x_2998_);
return v___x_2999_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3002_ = l_Lean_stringToMessageData(v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3003_, lean_object* v_positions_3004_, lean_object* v_recFnNames_3005_, lean_object* v_containsRecFn_3006_, lean_object* v_below_3007_, lean_object* v_e_3008_, lean_object* v_x_3009_, lean_object* v_x_3010_, lean_object* v_x_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
if (lean_obj_tag(v_x_3009_) == 5)
{
lean_object* v_fn_3018_; lean_object* v_arg_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_fn_3018_ = lean_ctor_get(v_x_3009_, 0);
lean_inc_ref(v_fn_3018_);
v_arg_3019_ = lean_ctor_get(v_x_3009_, 1);
lean_inc_ref(v_arg_3019_);
lean_dec_ref_known(v_x_3009_, 2);
v___x_3020_ = lean_array_set(v_x_3010_, v_x_3011_, v_arg_3019_);
v___x_3021_ = lean_unsigned_to_nat(1u);
v___x_3022_ = lean_nat_sub(v_x_3011_, v___x_3021_);
lean_dec(v_x_3011_);
v_x_3009_ = v_fn_3018_;
v_x_3010_ = v___x_3020_;
v_x_3011_ = v___x_3022_;
goto _start;
}
else
{
lean_object* v___f_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_dec(v_x_3011_);
lean_inc_ref(v_x_3009_);
v___f_3024_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3024_, 0, v_x_3009_);
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3024_, v_recArgInfos_3003_, v___x_3025_);
if (lean_obj_tag(v___x_3026_) == 1)
{
lean_object* v_val_3027_; lean_object* v___x_3028_; lean_object* v___y_3030_; lean_object* v_recArgPos_3056_; lean_object* v_indGroupInst_3057_; lean_object* v___x_3058_; uint8_t v___x_3059_; 
lean_dec_ref(v_x_3009_);
v_val_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_val_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = lean_array_fget_borrowed(v_recArgInfos_3003_, v_val_3027_);
v_recArgPos_3056_ = lean_ctor_get(v___x_3028_, 2);
v_indGroupInst_3057_ = lean_ctor_get(v___x_3028_, 4);
v___x_3058_ = lean_array_get_size(v_x_3010_);
v___x_3059_ = lean_nat_dec_lt(v_recArgPos_3056_, v___x_3058_);
if (v___x_3059_ == 0)
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_dec(v_val_3027_);
lean_dec_ref(v_x_3010_);
lean_dec_ref(v_below_3007_);
lean_dec_ref(v_containsRecFn_3006_);
lean_dec_ref(v_recFnNames_3005_);
lean_dec_ref(v_positions_3004_);
lean_dec_ref(v_recArgInfos_3003_);
v___x_3060_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3061_ = l_Lean_indentExpr(v_e_3008_);
v___x_3062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3060_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
v___x_3063_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3062_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
return v___x_3063_;
}
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_array_fget_borrowed(v_x_3010_, v_recArgPos_3056_);
lean_inc_ref(v___y_3015_);
lean_inc(v___x_3064_);
lean_inc_ref(v_below_3007_);
lean_inc_ref(v_containsRecFn_3006_);
lean_inc_ref(v_recFnNames_3005_);
lean_inc_ref(v_positions_3004_);
lean_inc_ref(v_recArgInfos_3003_);
v___x_3065_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3003_, v_positions_3004_, v_recFnNames_3005_, v_containsRecFn_3006_, v_below_3007_, v___x_3064_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v_params_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v_params_3067_ = lean_ctor_get(v_indGroupInst_3057_, 2);
v___x_3068_ = lean_array_get_size(v_params_3067_);
lean_inc_ref(v_positions_3004_);
lean_inc_ref(v_below_3007_);
v___x_3069_ = l_Lean_Elab_Structural_toBelow(v_below_3007_, v___x_3068_, v_positions_3004_, v_val_3027_, v_a_3066_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_dec_ref(v_e_3008_);
v___y_3030_ = v___x_3069_;
goto v___jp_3029_;
}
else
{
lean_object* v_a_3070_; uint8_t v___y_3072_; uint8_t v___x_3077_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
v___x_3077_ = l_Lean_Exception_isInterrupt(v_a_3070_);
if (v___x_3077_ == 0)
{
uint8_t v___x_3078_; 
v___x_3078_ = l_Lean_Exception_isRuntime(v_a_3070_);
v___y_3072_ = v___x_3078_;
goto v___jp_3071_;
}
else
{
lean_dec(v_a_3070_);
v___y_3072_ = v___x_3077_;
goto v___jp_3071_;
}
v___jp_3071_:
{
if (v___y_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec_ref_known(v___x_3069_, 1);
v___x_3073_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3074_ = l_Lean_indentExpr(v_e_3008_);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3075_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
v___y_3030_ = v___x_3076_;
goto v___jp_3029_;
}
else
{
lean_dec_ref(v_e_3008_);
v___y_3030_ = v___x_3069_;
goto v___jp_3029_;
}
}
}
}
else
{
lean_dec(v_val_3027_);
lean_dec_ref(v_x_3010_);
lean_dec_ref(v_e_3008_);
lean_dec_ref(v_below_3007_);
lean_dec_ref(v_containsRecFn_3006_);
lean_dec_ref(v_recFnNames_3005_);
lean_dec_ref(v_positions_3004_);
lean_dec_ref(v_recArgInfos_3003_);
return v___x_3065_;
}
}
v___jp_3029_:
{
if (lean_obj_tag(v___y_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_fixedParamPerm_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v_snd_3035_; size_t v_sz_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v_a_3031_ = lean_ctor_get(v___y_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___y_3030_, 1);
v_fixedParamPerm_3032_ = lean_ctor_get(v___x_3028_, 1);
v___x_3033_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3032_, v_x_3010_);
lean_dec_ref(v_x_3010_);
lean_inc(v___x_3028_);
v___x_3034_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3028_, v___x_3033_);
v_snd_3035_ = lean_ctor_get(v___x_3034_, 1);
lean_inc(v_snd_3035_);
lean_dec_ref(v___x_3034_);
v_sz_3036_ = lean_array_size(v_snd_3035_);
v___x_3037_ = ((size_t)0ULL);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3003_, v_positions_3004_, v_recFnNames_3005_, v_containsRecFn_3006_, v_below_3007_, v_sz_3036_, v___x_3037_, v_snd_3035_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3047_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3041_ = v___x_3038_;
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3038_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3047_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
v___x_3043_ = l_Lean_mkAppN(v_a_3031_, v_a_3039_);
lean_dec(v_a_3039_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 0, v___x_3043_);
v___x_3045_ = v___x_3041_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_3031_);
v_a_3048_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3038_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3038_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_dec_ref(v_x_3010_);
lean_dec_ref(v_below_3007_);
lean_dec_ref(v_containsRecFn_3006_);
lean_dec_ref(v_recFnNames_3005_);
lean_dec_ref(v_positions_3004_);
lean_dec_ref(v_recArgInfos_3003_);
return v___y_3030_;
}
}
}
else
{
lean_object* v___x_3079_; 
lean_dec(v___x_3026_);
lean_dec_ref(v_e_3008_);
lean_inc_ref(v___y_3015_);
lean_inc_ref(v_below_3007_);
lean_inc_ref(v_containsRecFn_3006_);
lean_inc_ref(v_recFnNames_3005_);
lean_inc_ref(v_positions_3004_);
lean_inc_ref(v_recArgInfos_3003_);
v___x_3079_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3003_, v_positions_3004_, v_recFnNames_3005_, v_containsRecFn_3006_, v_below_3007_, v_x_3009_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_3083_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v_sz_3081_ = lean_array_size(v_x_3010_);
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3003_, v_positions_3004_, v_recFnNames_3005_, v_containsRecFn_3006_, v_below_3007_, v_sz_3081_, v___x_3082_, v_x_3010_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3092_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3086_ = v___x_3083_;
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3083_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3092_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3088_; lean_object* v___x_3090_; 
v___x_3088_ = l_Lean_mkAppN(v_a_3080_, v_a_3084_);
lean_dec(v_a_3084_);
if (v_isShared_3087_ == 0)
{
lean_ctor_set(v___x_3086_, 0, v___x_3088_);
v___x_3090_ = v___x_3086_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec(v_a_3080_);
v_a_3093_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3083_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3083_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
lean_dec_ref(v_x_3010_);
lean_dec_ref(v_below_3007_);
lean_dec_ref(v_containsRecFn_3006_);
lean_dec_ref(v_recFnNames_3005_);
lean_dec_ref(v_positions_3004_);
lean_dec_ref(v_recArgInfos_3003_);
return v___x_3079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3101_, lean_object* v_recArgInfos_3102_, lean_object* v_positions_3103_, lean_object* v_recFnNames_3104_, lean_object* v_containsRecFn_3105_, lean_object* v_below_3106_, uint8_t v___x_3107_, uint8_t v_a_3108_, lean_object* v_x_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_expr_instantiate1(v_body_3101_, v_x_3109_);
lean_inc_ref(v___y_3113_);
v___x_3117_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3102_, v_positions_3103_, v_recFnNames_3104_, v_containsRecFn_3105_, v_below_3106_, v___x_3116_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; lean_object* v___x_3123_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = lean_unsigned_to_nat(1u);
v___x_3120_ = lean_mk_empty_array_with_capacity(v___x_3119_);
v___x_3121_ = lean_array_push(v___x_3120_, v_x_3109_);
v___x_3122_ = 1;
v___x_3123_ = l_Lean_Meta_mkLambdaFVars(v___x_3121_, v_a_3118_, v___x_3107_, v_a_3108_, v___x_3107_, v_a_3108_, v___x_3122_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
lean_dec_ref(v___x_3121_);
return v___x_3123_;
}
else
{
lean_dec_ref(v_x_3109_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3124_, lean_object* v_recArgInfos_3125_, lean_object* v_positions_3126_, lean_object* v_recFnNames_3127_, lean_object* v_containsRecFn_3128_, lean_object* v_below_3129_, lean_object* v___x_3130_, lean_object* v_a_3131_, lean_object* v_x_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
uint8_t v___x_28580__boxed_3139_; uint8_t v_a_28581__boxed_3140_; lean_object* v_res_3141_; 
v___x_28580__boxed_3139_ = lean_unbox(v___x_3130_);
v_a_28581__boxed_3140_ = lean_unbox(v_a_3131_);
v_res_3141_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3124_, v_recArgInfos_3125_, v_positions_3126_, v_recFnNames_3127_, v_containsRecFn_3128_, v_below_3129_, v___x_28580__boxed_3139_, v_a_28581__boxed_3140_, v_x_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v_body_3124_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3142_, lean_object* v_recArgInfos_3143_, lean_object* v_positions_3144_, lean_object* v_recFnNames_3145_, lean_object* v_containsRecFn_3146_, lean_object* v_below_3147_, uint8_t v___x_3148_, uint8_t v_a_3149_, lean_object* v_x_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_expr_instantiate1(v_body_3142_, v_x_3150_);
lean_inc_ref(v___y_3154_);
v___x_3158_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3143_, v_positions_3144_, v_recFnNames_3145_, v_containsRecFn_3146_, v_below_3147_, v___x_3157_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; lean_object* v___x_3164_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_a_3159_);
lean_dec_ref_known(v___x_3158_, 1);
v___x_3160_ = lean_unsigned_to_nat(1u);
v___x_3161_ = lean_mk_empty_array_with_capacity(v___x_3160_);
v___x_3162_ = lean_array_push(v___x_3161_, v_x_3150_);
v___x_3163_ = 1;
v___x_3164_ = l_Lean_Meta_mkForallFVars(v___x_3162_, v_a_3159_, v___x_3148_, v_a_3149_, v_a_3149_, v___x_3163_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec_ref(v___x_3162_);
return v___x_3164_;
}
else
{
lean_dec_ref(v_x_3150_);
return v___x_3158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3165_, lean_object* v_recArgInfos_3166_, lean_object* v_positions_3167_, lean_object* v_recFnNames_3168_, lean_object* v_containsRecFn_3169_, lean_object* v_below_3170_, lean_object* v___x_3171_, lean_object* v_a_3172_, lean_object* v_x_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
uint8_t v___x_28598__boxed_3180_; uint8_t v_a_28599__boxed_3181_; lean_object* v_res_3182_; 
v___x_28598__boxed_3180_ = lean_unbox(v___x_3171_);
v_a_28599__boxed_3181_ = lean_unbox(v_a_3172_);
v_res_3182_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3165_, v_recArgInfos_3166_, v_positions_3167_, v_recFnNames_3168_, v_containsRecFn_3169_, v_below_3170_, v___x_28598__boxed_3180_, v_a_28599__boxed_3181_, v_x_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v_body_3165_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3183_, lean_object* v_recArgInfos_3184_, lean_object* v_positions_3185_, lean_object* v_recFnNames_3186_, lean_object* v_containsRecFn_3187_, lean_object* v_below_3188_, lean_object* v_x_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3183_, v_recArgInfos_3184_, v_positions_3185_, v_recFnNames_3186_, v_containsRecFn_3187_, v_below_3188_, v_x_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v_x_3189_);
lean_dec_ref(v_body_3183_);
return v_res_3196_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3201_ = l_Lean_stringToMessageData(v___x_3200_);
return v___x_3201_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3204_ = l_Lean_stringToMessageData(v___x_3203_);
return v___x_3204_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3207_ = l_Lean_stringToMessageData(v___x_3206_);
return v___x_3207_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3210_ = l_Lean_stringToMessageData(v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3211_, lean_object* v_b_3212_, lean_object* v_recArgInfos_3213_, lean_object* v_positions_3214_, lean_object* v_recFnNames_3215_, lean_object* v_containsRecFn_3216_, uint8_t v___x_3217_, uint8_t v_a_3218_, lean_object* v___x_3219_, lean_object* v_a_3220_, lean_object* v_e_3221_, lean_object* v___x_3222_, lean_object* v_xs_3223_, lean_object* v_altBody_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v_toCold_3266_; lean_object* v_options_3267_; uint8_t v_hasTrace_3268_; 
v_toCold_3266_ = lean_ctor_get(v___y_3228_, 0);
v_options_3267_ = lean_ctor_get(v_toCold_3266_, 2);
v_hasTrace_3268_ = lean_ctor_get_uint8(v_options_3267_, sizeof(void*)*1);
if (v_hasTrace_3268_ == 0)
{
lean_dec(v___x_3222_);
v___y_3243_ = v___y_3225_;
v___y_3244_ = v___y_3226_;
v___y_3245_ = v___y_3227_;
v___y_3246_ = v___y_3228_;
v___y_3247_ = v___y_3229_;
goto v___jp_3242_;
}
else
{
lean_object* v_inheritedTraceOptions_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; uint8_t v___x_3272_; 
v_inheritedTraceOptions_3269_ = lean_ctor_get(v_toCold_3266_, 11);
v___x_3270_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3222_);
v___x_3271_ = l_Lean_Name_append(v___x_3270_, v___x_3222_);
v___x_3272_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3269_, v_options_3267_, v___x_3271_);
lean_dec(v___x_3271_);
if (v___x_3272_ == 0)
{
lean_dec(v___x_3222_);
v___y_3243_ = v___y_3225_;
v___y_3244_ = v___y_3226_;
v___y_3245_ = v___y_3227_;
v___y_3246_ = v___y_3228_;
v___y_3247_ = v___y_3229_;
goto v___jp_3242_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3273_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3212_);
v___x_3274_ = l_Nat_reprFast(v_b_3212_);
v___x_3275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
v___x_3276_ = l_Lean_MessageData_ofFormat(v___x_3275_);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3273_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
lean_inc_ref(v_xs_3223_);
v___x_3280_ = lean_array_to_list(v_xs_3223_);
v___x_3281_ = lean_box(0);
v___x_3282_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3280_, v___x_3281_);
v___x_3283_ = l_Lean_MessageData_ofList(v___x_3282_);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3279_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3222_, v___x_3284_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_dec_ref_known(v___x_3285_, 1);
v___y_3243_ = v___y_3225_;
v___y_3244_ = v___y_3226_;
v___y_3245_ = v___y_3227_;
v___y_3246_ = v___y_3228_;
v___y_3247_ = v___y_3229_;
goto v___jp_3242_;
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec_ref(v_altBody_3224_);
lean_dec_ref(v_xs_3223_);
lean_dec_ref(v_e_3221_);
lean_dec_ref(v_a_3220_);
lean_dec_ref(v_containsRecFn_3216_);
lean_dec_ref(v_recFnNames_3215_);
lean_dec_ref(v_positions_3214_);
lean_dec_ref(v_recArgInfos_3213_);
lean_dec(v_b_3212_);
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3285_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3285_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
v___jp_3231_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_array_get_borrowed(v___x_3211_, v_xs_3223_, v_b_3212_);
lean_dec(v_b_3212_);
lean_inc_ref(v___y_3235_);
lean_inc(v___x_3237_);
v___x_3238_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3213_, v_positions_3214_, v_recFnNames_3215_, v_containsRecFn_3216_, v___x_3237_, v_altBody_3224_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; uint8_t v___x_3240_; lean_object* v___x_3241_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref_known(v___x_3238_, 1);
v___x_3240_ = 1;
v___x_3241_ = l_Lean_Meta_mkLambdaFVars(v_xs_3223_, v_a_3239_, v___x_3217_, v_a_3218_, v___x_3217_, v_a_3218_, v___x_3240_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec_ref(v_xs_3223_);
return v___x_3241_;
}
else
{
lean_dec_ref(v_xs_3223_);
return v___x_3238_;
}
}
v___jp_3242_:
{
lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3248_ = lean_array_get_size(v_xs_3223_);
v___x_3249_ = lean_nat_dec_eq(v___x_3248_, v___x_3219_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_altBody_3224_);
lean_dec_ref(v_xs_3223_);
lean_dec_ref(v_containsRecFn_3216_);
lean_dec_ref(v_recFnNames_3215_);
lean_dec_ref(v_positions_3214_);
lean_dec_ref(v_recArgInfos_3213_);
lean_dec(v_b_3212_);
v___x_3250_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3251_ = l_Lean_indentExpr(v_a_3220_);
v___x_3252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_indentExpr(v_e_3221_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3256_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3257_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3257_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
else
{
lean_dec_ref(v_e_3221_);
lean_dec_ref(v_a_3220_);
v___y_3232_ = v___y_3243_;
v___y_3233_ = v___y_3244_;
v___y_3234_ = v___y_3245_;
v___y_3235_ = v___y_3246_;
v___y_3236_ = v___y_3247_;
goto v___jp_3231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3294_ = _args[0];
lean_object* v_b_3295_ = _args[1];
lean_object* v_recArgInfos_3296_ = _args[2];
lean_object* v_positions_3297_ = _args[3];
lean_object* v_recFnNames_3298_ = _args[4];
lean_object* v_containsRecFn_3299_ = _args[5];
lean_object* v___x_3300_ = _args[6];
lean_object* v_a_3301_ = _args[7];
lean_object* v___x_3302_ = _args[8];
lean_object* v_a_3303_ = _args[9];
lean_object* v_e_3304_ = _args[10];
lean_object* v___x_3305_ = _args[11];
lean_object* v_xs_3306_ = _args[12];
lean_object* v_altBody_3307_ = _args[13];
lean_object* v___y_3308_ = _args[14];
lean_object* v___y_3309_ = _args[15];
lean_object* v___y_3310_ = _args[16];
lean_object* v___y_3311_ = _args[17];
lean_object* v___y_3312_ = _args[18];
lean_object* v___y_3313_ = _args[19];
_start:
{
uint8_t v___x_28674__boxed_3314_; uint8_t v_a_28675__boxed_3315_; lean_object* v_res_3316_; 
v___x_28674__boxed_3314_ = lean_unbox(v___x_3300_);
v_a_28675__boxed_3315_ = lean_unbox(v_a_3301_);
v_res_3316_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3294_, v_b_3295_, v_recArgInfos_3296_, v_positions_3297_, v_recFnNames_3298_, v_containsRecFn_3299_, v___x_28674__boxed_3314_, v_a_28675__boxed_3315_, v___x_3302_, v_a_3303_, v_e_3304_, v___x_3305_, v_xs_3306_, v_altBody_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec(v___x_3302_);
lean_dec_ref(v___x_3294_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3317_, lean_object* v_positions_3318_, lean_object* v_recFnNames_3319_, lean_object* v_containsRecFn_3320_, uint8_t v_a_3321_, lean_object* v_e_3322_, lean_object* v_as_3323_, lean_object* v_bs_3324_, lean_object* v_i_3325_, lean_object* v_cs_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = lean_array_get_size(v_as_3323_);
v___x_3334_ = lean_nat_dec_lt(v_i_3325_, v___x_3333_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; 
lean_dec(v_i_3325_);
lean_dec_ref(v_e_3322_);
lean_dec_ref(v_containsRecFn_3320_);
lean_dec_ref(v_recFnNames_3319_);
lean_dec_ref(v_positions_3318_);
lean_dec_ref(v_recArgInfos_3317_);
v___x_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3335_, 0, v_cs_3326_);
return v___x_3335_;
}
else
{
lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3336_ = lean_array_get_size(v_bs_3324_);
v___x_3337_ = lean_nat_dec_lt(v_i_3325_, v___x_3336_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; 
lean_dec(v_i_3325_);
lean_dec_ref(v_e_3322_);
lean_dec_ref(v_containsRecFn_3320_);
lean_dec_ref(v_recFnNames_3319_);
lean_dec_ref(v_positions_3318_);
lean_dec_ref(v_recArgInfos_3317_);
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_cs_3326_);
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v_a_3342_; lean_object* v_b_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; 
v___x_3339_ = l_Lean_instInhabitedExpr;
v___x_3340_ = 0;
v___x_3341_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3342_ = lean_array_fget_borrowed(v_as_3323_, v_i_3325_);
v_b_3343_ = lean_array_fget_borrowed(v_bs_3324_, v_i_3325_);
v___x_3344_ = lean_unsigned_to_nat(1u);
v___x_3345_ = lean_nat_add(v_b_3343_, v___x_3344_);
v___x_3346_ = lean_box(v___x_3340_);
v___x_3347_ = lean_box(v_a_3321_);
lean_inc_ref(v_e_3322_);
lean_inc_n(v_a_3342_, 2);
lean_inc(v___x_3345_);
lean_inc_ref(v_containsRecFn_3320_);
lean_inc_ref(v_recFnNames_3319_);
lean_inc_ref(v_positions_3318_);
lean_inc_ref(v_recArgInfos_3317_);
lean_inc(v_b_3343_);
v___f_3348_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3348_, 0, v___x_3339_);
lean_closure_set(v___f_3348_, 1, v_b_3343_);
lean_closure_set(v___f_3348_, 2, v_recArgInfos_3317_);
lean_closure_set(v___f_3348_, 3, v_positions_3318_);
lean_closure_set(v___f_3348_, 4, v_recFnNames_3319_);
lean_closure_set(v___f_3348_, 5, v_containsRecFn_3320_);
lean_closure_set(v___f_3348_, 6, v___x_3346_);
lean_closure_set(v___f_3348_, 7, v___x_3347_);
lean_closure_set(v___f_3348_, 8, v___x_3345_);
lean_closure_set(v___f_3348_, 9, v_a_3342_);
lean_closure_set(v___f_3348_, 10, v_e_3322_);
lean_closure_set(v___f_3348_, 11, v___x_3341_);
v___x_3349_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3342_, v___x_3345_, v___f_3348_, v___x_3340_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
v___x_3351_ = lean_nat_add(v_i_3325_, v___x_3344_);
lean_dec(v_i_3325_);
v___x_3352_ = lean_array_push(v_cs_3326_, v_a_3350_);
v_i_3325_ = v___x_3351_;
v_cs_3326_ = v___x_3352_;
goto _start;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3361_; 
lean_dec_ref(v_cs_3326_);
lean_dec(v_i_3325_);
lean_dec_ref(v_e_3322_);
lean_dec_ref(v_containsRecFn_3320_);
lean_dec_ref(v_recFnNames_3319_);
lean_dec_ref(v_positions_3318_);
lean_dec_ref(v_recArgInfos_3317_);
v_a_3354_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3356_ = v___x_3349_;
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3349_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3361_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
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
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
return v___x_3364_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3367_ = l_Lean_stringToMessageData(v___x_3366_);
return v___x_3367_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3370_ = l_Lean_stringToMessageData(v___x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3371_, lean_object* v_positions_3372_, lean_object* v_recFnNames_3373_, lean_object* v_containsRecFn_3374_, lean_object* v_below_3375_, lean_object* v_e_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_e_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___x_3396_; 
lean_inc_ref(v_containsRecFn_3374_);
lean_inc(v_a_3381_);
lean_inc_ref(v_a_3380_);
lean_inc(v_a_3379_);
lean_inc_ref(v_a_3378_);
lean_inc(v_a_3377_);
lean_inc_ref(v_e_3376_);
v___x_3396_ = lean_apply_7(v_containsRecFn_3374_, v_e_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, lean_box(0));
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3611_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3399_ = v___x_3396_;
v_isShared_3400_ = v_isSharedCheck_3611_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3396_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3611_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
uint8_t v___x_3401_; 
v___x_3401_ = lean_unbox(v_a_3397_);
if (v___x_3401_ == 0)
{
lean_object* v___x_3403_; 
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
if (v_isShared_3400_ == 0)
{
lean_ctor_set(v___x_3399_, 0, v_e_3376_);
v___x_3403_ = v___x_3399_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_e_3376_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
else
{
uint8_t v___x_3405_; 
lean_del_object(v___x_3399_);
v___x_3405_ = 0;
switch(lean_obj_tag(v_e_3376_))
{
case 6:
{
lean_object* v_binderName_3406_; lean_object* v_binderType_3407_; lean_object* v_body_3408_; uint8_t v_binderInfo_3409_; lean_object* v___x_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; 
v_binderName_3406_ = lean_ctor_get(v_e_3376_, 0);
lean_inc(v_binderName_3406_);
v_binderType_3407_ = lean_ctor_get(v_e_3376_, 1);
lean_inc_ref(v_binderType_3407_);
v_body_3408_ = lean_ctor_get(v_e_3376_, 2);
lean_inc_ref(v_body_3408_);
v_binderInfo_3409_ = lean_ctor_get_uint8(v_e_3376_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3376_, 3);
v___x_3410_ = lean_box(v___x_3405_);
lean_inc_ref(v_below_3375_);
lean_inc_ref(v_containsRecFn_3374_);
lean_inc_ref(v_recFnNames_3373_);
lean_inc_ref(v_positions_3372_);
lean_inc_ref(v_recArgInfos_3371_);
v___f_3411_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3411_, 0, v_body_3408_);
lean_closure_set(v___f_3411_, 1, v_recArgInfos_3371_);
lean_closure_set(v___f_3411_, 2, v_positions_3372_);
lean_closure_set(v___f_3411_, 3, v_recFnNames_3373_);
lean_closure_set(v___f_3411_, 4, v_containsRecFn_3374_);
lean_closure_set(v___f_3411_, 5, v_below_3375_);
lean_closure_set(v___f_3411_, 6, v___x_3410_);
lean_closure_set(v___f_3411_, 7, v_a_3397_);
lean_inc_ref(v_a_3380_);
v___x_3412_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v_below_3375_, v_binderType_3407_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v___x_3414_ = 0;
v___x_3415_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3406_, v_binderInfo_3409_, v_a_3413_, v___f_3411_, v___x_3414_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec_ref(v_a_3380_);
return v___x_3415_;
}
else
{
lean_dec_ref(v___f_3411_);
lean_dec(v_binderName_3406_);
lean_dec_ref(v_a_3380_);
return v___x_3412_;
}
}
case 7:
{
lean_object* v_binderName_3416_; lean_object* v_binderType_3417_; lean_object* v_body_3418_; uint8_t v_binderInfo_3419_; lean_object* v___x_3420_; lean_object* v___f_3421_; lean_object* v___x_3422_; 
v_binderName_3416_ = lean_ctor_get(v_e_3376_, 0);
lean_inc(v_binderName_3416_);
v_binderType_3417_ = lean_ctor_get(v_e_3376_, 1);
lean_inc_ref(v_binderType_3417_);
v_body_3418_ = lean_ctor_get(v_e_3376_, 2);
lean_inc_ref(v_body_3418_);
v_binderInfo_3419_ = lean_ctor_get_uint8(v_e_3376_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3376_, 3);
v___x_3420_ = lean_box(v___x_3405_);
lean_inc_ref(v_below_3375_);
lean_inc_ref(v_containsRecFn_3374_);
lean_inc_ref(v_recFnNames_3373_);
lean_inc_ref(v_positions_3372_);
lean_inc_ref(v_recArgInfos_3371_);
v___f_3421_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3421_, 0, v_body_3418_);
lean_closure_set(v___f_3421_, 1, v_recArgInfos_3371_);
lean_closure_set(v___f_3421_, 2, v_positions_3372_);
lean_closure_set(v___f_3421_, 3, v_recFnNames_3373_);
lean_closure_set(v___f_3421_, 4, v_containsRecFn_3374_);
lean_closure_set(v___f_3421_, 5, v_below_3375_);
lean_closure_set(v___f_3421_, 6, v___x_3420_);
lean_closure_set(v___f_3421_, 7, v_a_3397_);
lean_inc_ref(v_a_3380_);
v___x_3422_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v_below_3375_, v_binderType_3417_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_a_3423_);
lean_dec_ref_known(v___x_3422_, 1);
v___x_3424_ = 0;
v___x_3425_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3416_, v_binderInfo_3419_, v_a_3423_, v___f_3421_, v___x_3424_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec_ref(v_a_3380_);
return v___x_3425_;
}
else
{
lean_dec_ref(v___f_3421_);
lean_dec(v_binderName_3416_);
lean_dec_ref(v_a_3380_);
return v___x_3422_;
}
}
case 8:
{
lean_object* v_declName_3426_; lean_object* v_type_3427_; lean_object* v_value_3428_; lean_object* v_body_3429_; uint8_t v_nondep_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; 
lean_dec(v_a_3397_);
v_declName_3426_ = lean_ctor_get(v_e_3376_, 0);
lean_inc(v_declName_3426_);
v_type_3427_ = lean_ctor_get(v_e_3376_, 1);
lean_inc_ref(v_type_3427_);
v_value_3428_ = lean_ctor_get(v_e_3376_, 2);
lean_inc_ref(v_value_3428_);
v_body_3429_ = lean_ctor_get(v_e_3376_, 3);
lean_inc_ref(v_body_3429_);
v_nondep_3430_ = lean_ctor_get_uint8(v_e_3376_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3376_, 4);
lean_inc_ref_n(v_below_3375_, 2);
lean_inc_ref_n(v_containsRecFn_3374_, 2);
lean_inc_ref_n(v_recFnNames_3373_, 2);
lean_inc_ref_n(v_positions_3372_, 2);
lean_inc_ref_n(v_recArgInfos_3371_, 2);
v___f_3431_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3431_, 0, v_body_3429_);
lean_closure_set(v___f_3431_, 1, v_recArgInfos_3371_);
lean_closure_set(v___f_3431_, 2, v_positions_3372_);
lean_closure_set(v___f_3431_, 3, v_recFnNames_3373_);
lean_closure_set(v___f_3431_, 4, v_containsRecFn_3374_);
lean_closure_set(v___f_3431_, 5, v_below_3375_);
lean_inc_ref(v_a_3380_);
v___x_3432_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v_below_3375_, v_type_3427_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3432_, 1);
lean_inc_ref(v_a_3380_);
v___x_3434_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v_below_3375_, v_value_3428_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; uint8_t v___x_3436_; lean_object* v___x_3437_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
v___x_3436_ = 0;
v___x_3437_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3426_, v_a_3433_, v_a_3435_, v___f_3431_, v_nondep_3430_, v___x_3436_, v___x_3405_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec_ref(v_a_3380_);
return v___x_3437_;
}
else
{
lean_dec(v_a_3433_);
lean_dec_ref(v___f_3431_);
lean_dec(v_declName_3426_);
lean_dec_ref(v_a_3380_);
return v___x_3434_;
}
}
else
{
lean_dec_ref(v___f_3431_);
lean_dec_ref(v_value_3428_);
lean_dec(v_declName_3426_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
return v___x_3432_;
}
}
case 10:
{
lean_object* v_data_3438_; lean_object* v_expr_3439_; lean_object* v___x_3440_; 
lean_dec(v_a_3397_);
v_data_3438_ = lean_ctor_get(v_e_3376_, 0);
lean_inc(v_data_3438_);
v_expr_3439_ = lean_ctor_get(v_e_3376_, 1);
lean_inc_ref(v_expr_3439_);
v___x_3440_ = l_Lean_getRecAppSyntax_x3f(v_e_3376_);
lean_dec_ref_known(v_e_3376_, 2);
if (lean_obj_tag(v___x_3440_) == 1)
{
lean_object* v_val_3441_; lean_object* v_toCold_3442_; lean_object* v_currRecDepth_3443_; lean_object* v_ref_3444_; uint16_t v_optionFlags_3445_; uint8_t v_suppressElabErrors_3446_; uint8_t v_isRecordingDeps_3447_; lean_object* v_ref_3448_; lean_object* v___x_3449_; 
lean_dec(v_data_3438_);
v_val_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_val_3441_);
lean_dec_ref_known(v___x_3440_, 1);
v_toCold_3442_ = lean_ctor_get(v_a_3380_, 0);
lean_inc_ref(v_toCold_3442_);
v_currRecDepth_3443_ = lean_ctor_get(v_a_3380_, 1);
lean_inc(v_currRecDepth_3443_);
v_ref_3444_ = lean_ctor_get(v_a_3380_, 2);
lean_inc(v_ref_3444_);
v_optionFlags_3445_ = lean_ctor_get_uint16(v_a_3380_, sizeof(void*)*3);
v_suppressElabErrors_3446_ = lean_ctor_get_uint8(v_a_3380_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3447_ = lean_ctor_get_uint8(v_a_3380_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_3380_);
v_ref_3448_ = l_Lean_replaceRef(v_val_3441_, v_ref_3444_);
lean_dec(v_ref_3444_);
lean_dec(v_val_3441_);
v___x_3449_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3449_, 0, v_toCold_3442_);
lean_ctor_set(v___x_3449_, 1, v_currRecDepth_3443_);
lean_ctor_set(v___x_3449_, 2, v_ref_3448_);
lean_ctor_set_uint16(v___x_3449_, sizeof(void*)*3, v_optionFlags_3445_);
lean_ctor_set_uint8(v___x_3449_, sizeof(void*)*3 + 2, v_suppressElabErrors_3446_);
lean_ctor_set_uint8(v___x_3449_, sizeof(void*)*3 + 3, v_isRecordingDeps_3447_);
v_e_3376_ = v_expr_3439_;
v_a_3380_ = v___x_3449_;
goto _start;
}
else
{
lean_object* v___x_3451_; 
lean_dec(v___x_3440_);
v___x_3451_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v_below_3375_, v_expr_3439_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3460_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3454_ = v___x_3451_;
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; 
v___x_3456_ = l_Lean_mkMData(v_data_3438_, v_a_3452_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v___x_3456_);
v___x_3458_ = v___x_3454_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
else
{
lean_dec(v_data_3438_);
return v___x_3451_;
}
}
}
case 11:
{
lean_object* v_typeName_3461_; lean_object* v_idx_3462_; lean_object* v_struct_3463_; lean_object* v___x_3464_; 
lean_dec(v_a_3397_);
v_typeName_3461_ = lean_ctor_get(v_e_3376_, 0);
lean_inc(v_typeName_3461_);
v_idx_3462_ = lean_ctor_get(v_e_3376_, 1);
lean_inc(v_idx_3462_);
v_struct_3463_ = lean_ctor_get(v_e_3376_, 2);
lean_inc_ref(v_struct_3463_);
lean_dec_ref_known(v_e_3376_, 3);
v___x_3464_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v_below_3375_, v_struct_3463_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3473_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3467_ = v___x_3464_;
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3473_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3469_ = l_Lean_mkProj(v_typeName_3461_, v_idx_3462_, v_a_3465_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 0, v___x_3469_);
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v___x_3469_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
else
{
lean_dec(v_idx_3462_);
lean_dec(v_typeName_3461_);
return v___x_3464_;
}
}
case 5:
{
uint8_t v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = lean_unbox(v_a_3397_);
lean_inc_ref(v_e_3376_);
v___x_3475_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3376_, v___x_3474_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
if (lean_obj_tag(v_a_3476_) == 0)
{
lean_dec(v_a_3397_);
v_e_3384_ = v_e_3376_;
v___y_3385_ = v_a_3377_;
v___y_3386_ = v_a_3378_;
v___y_3387_ = v_a_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
goto v___jp_3383_;
}
else
{
lean_object* v_val_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v_val_3477_ = lean_ctor_get(v_a_3476_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_a_3476_, 1);
v___x_3478_ = lean_unsigned_to_nat(0u);
v___x_3479_ = lean_array_get_size(v_recArgInfos_3371_);
v___x_3480_ = lean_nat_dec_lt(v___x_3478_, v___x_3479_);
if (v___x_3480_ == 0)
{
lean_dec(v_val_3477_);
lean_dec(v_a_3397_);
v_e_3384_ = v_e_3376_;
v___y_3385_ = v_a_3377_;
v___y_3386_ = v_a_3378_;
v___y_3387_ = v_a_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
goto v___jp_3383_;
}
else
{
if (v___x_3480_ == 0)
{
lean_dec(v_val_3477_);
lean_dec(v_a_3397_);
v_e_3384_ = v_e_3376_;
v___y_3385_ = v_a_3377_;
v___y_3386_ = v_a_3378_;
v___y_3387_ = v_a_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
goto v___jp_3383_;
}
else
{
size_t v___x_3481_; size_t v___x_3482_; uint8_t v___x_3483_; 
v___x_3481_ = ((size_t)0ULL);
v___x_3482_ = lean_usize_of_nat(v___x_3479_);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3376_, v_recArgInfos_3371_, v___x_3481_, v___x_3482_);
if (v___x_3483_ == 0)
{
lean_dec(v_val_3477_);
lean_dec(v_a_3397_);
v_e_3384_ = v_e_3376_;
v___y_3385_ = v_a_3377_;
v___y_3386_ = v_a_3378_;
v___y_3387_ = v_a_3379_;
v___y_3388_ = v_a_3380_;
v___y_3389_ = v_a_3381_;
goto v___jp_3383_;
}
else
{
lean_object* v_toCold_3484_; lean_object* v_inheritedTraceOptions_3485_; lean_object* v___x_3486_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___x_3557_; 
v_toCold_3484_ = lean_ctor_get(v_a_3380_, 0);
v_inheritedTraceOptions_3485_ = lean_ctor_get(v_toCold_3484_, 11);
v___x_3486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3557_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3486_, v_inheritedTraceOptions_3485_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; uint8_t v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = lean_unbox(v_a_3558_);
lean_dec(v_a_3558_);
if (v___x_3559_ == 0)
{
v___y_3488_ = v_a_3377_;
v___y_3489_ = v_a_3378_;
v___y_3490_ = v_a_3379_;
v___y_3491_ = v_a_3380_;
v___y_3492_ = v_a_3381_;
goto v___jp_3487_;
}
else
{
lean_object* v___x_3560_; 
lean_inc(v_a_3381_);
lean_inc_ref(v_a_3380_);
lean_inc(v_a_3379_);
lean_inc_ref(v_a_3378_);
lean_inc_ref(v_below_3375_);
v___x_3560_ = lean_infer_type(v_below_3375_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
v___x_3562_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3375_);
v___x_3563_ = l_Lean_MessageData_ofExpr(v_below_3375_);
v___x_3564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3562_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3564_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = l_Lean_MessageData_ofExpr(v_a_3561_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3566_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3486_, v___x_3568_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_dec_ref_known(v___x_3569_, 1);
v___y_3488_ = v_a_3377_;
v___y_3489_ = v_a_3378_;
v___y_3490_ = v_a_3379_;
v___y_3491_ = v_a_3380_;
v___y_3492_ = v_a_3381_;
goto v___jp_3487_;
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v_val_3477_);
lean_dec_ref_known(v_e_3376_, 2);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
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
else
{
lean_dec(v_val_3477_);
lean_dec_ref_known(v_e_3376_, 2);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
return v___x_3560_;
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_val_3477_);
lean_dec_ref_known(v_e_3376_, 2);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
v_a_3578_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3557_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3557_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
v___jp_3487_:
{
lean_object* v___x_3493_; 
lean_inc_ref(v_below_3375_);
v___x_3493_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3477_, v_below_3375_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
if (lean_obj_tag(v_a_3494_) == 1)
{
lean_object* v_val_3495_; lean_object* v_toMatcherInfo_3496_; lean_object* v_matcherName_3497_; lean_object* v_matcherLevels_3498_; lean_object* v_params_3499_; lean_object* v_motive_3500_; lean_object* v_discrs_3501_; lean_object* v_alts_3502_; lean_object* v_remaining_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; lean_object* v___x_3507_; 
lean_dec_ref(v_below_3375_);
v_val_3495_ = lean_ctor_get(v_a_3494_, 0);
lean_inc(v_val_3495_);
lean_dec_ref_known(v_a_3494_, 1);
v_toMatcherInfo_3496_ = lean_ctor_get(v_val_3495_, 0);
lean_inc_ref(v_toMatcherInfo_3496_);
v_matcherName_3497_ = lean_ctor_get(v_val_3495_, 1);
lean_inc(v_matcherName_3497_);
v_matcherLevels_3498_ = lean_ctor_get(v_val_3495_, 2);
lean_inc_ref(v_matcherLevels_3498_);
v_params_3499_ = lean_ctor_get(v_val_3495_, 3);
lean_inc_ref(v_params_3499_);
v_motive_3500_ = lean_ctor_get(v_val_3495_, 4);
lean_inc_ref(v_motive_3500_);
v_discrs_3501_ = lean_ctor_get(v_val_3495_, 5);
lean_inc_ref(v_discrs_3501_);
v_alts_3502_ = lean_ctor_get(v_val_3495_, 6);
lean_inc_ref(v_alts_3502_);
v_remaining_3503_ = lean_ctor_get(v_val_3495_, 7);
lean_inc_ref(v_remaining_3503_);
v___x_3504_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3495_);
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3506_ = lean_unbox(v_a_3397_);
lean_dec(v_a_3397_);
v___x_3507_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v___x_3506_, v_e_3376_, v_alts_3502_, v___x_3504_, v___x_3478_, v___x_3505_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v___x_3504_);
lean_dec_ref(v_alts_3502_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3517_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3510_ = v___x_3507_;
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3507_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3517_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3512_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3512_, 0, v_toMatcherInfo_3496_);
lean_ctor_set(v___x_3512_, 1, v_matcherName_3497_);
lean_ctor_set(v___x_3512_, 2, v_matcherLevels_3498_);
lean_ctor_set(v___x_3512_, 3, v_params_3499_);
lean_ctor_set(v___x_3512_, 4, v_motive_3500_);
lean_ctor_set(v___x_3512_, 5, v_discrs_3501_);
lean_ctor_set(v___x_3512_, 6, v_a_3508_);
lean_ctor_set(v___x_3512_, 7, v_remaining_3503_);
v___x_3513_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3512_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 0, v___x_3513_);
v___x_3515_ = v___x_3510_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v_remaining_3503_);
lean_dec_ref(v_discrs_3501_);
lean_dec_ref(v_motive_3500_);
lean_dec_ref(v_params_3499_);
lean_dec_ref(v_matcherLevels_3498_);
lean_dec(v_matcherName_3497_);
lean_dec_ref(v_toMatcherInfo_3496_);
v_a_3518_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3507_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3507_);
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
else
{
lean_object* v_toCold_3526_; lean_object* v_inheritedTraceOptions_3527_; lean_object* v___x_3528_; 
lean_dec(v_a_3494_);
lean_dec(v_a_3397_);
v_toCold_3526_ = lean_ctor_get(v___y_3491_, 0);
v_inheritedTraceOptions_3527_ = lean_ctor_get(v_toCold_3526_, 11);
v___x_3528_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3486_, v_inheritedTraceOptions_3527_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; uint8_t v___x_3530_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = lean_unbox(v_a_3529_);
lean_dec(v_a_3529_);
if (v___x_3530_ == 0)
{
v_e_3384_ = v_e_3376_;
v___y_3385_ = v___y_3488_;
v___y_3386_ = v___y_3489_;
v___y_3387_ = v___y_3490_;
v___y_3388_ = v___y_3491_;
v___y_3389_ = v___y_3492_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3532_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3486_, v___x_3531_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_dec_ref_known(v___x_3532_, 1);
v_e_3384_ = v_e_3376_;
v___y_3385_ = v___y_3488_;
v___y_3386_ = v___y_3489_;
v___y_3387_ = v___y_3490_;
v___y_3388_ = v___y_3491_;
v___y_3389_ = v___y_3492_;
goto v___jp_3383_;
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec_ref(v___y_3491_);
lean_dec_ref_known(v_e_3376_, 2);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec_ref(v___y_3491_);
lean_dec_ref_known(v_e_3376_, 2);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
v_a_3541_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3528_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3528_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec_ref(v___y_3491_);
lean_dec_ref_known(v_e_3376_, 2);
lean_dec(v_a_3397_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
v_a_3549_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3493_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3493_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
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
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec_ref_known(v_e_3376_, 2);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
v_a_3586_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3475_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3475_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
default: 
{
lean_object* v___x_3594_; 
lean_dec(v_a_3397_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
lean_inc_ref(v_e_3376_);
v___x_3594_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3373_, v_e_3376_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec_ref(v_a_3380_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; 
v_unused_3602_ = lean_ctor_get(v___x_3594_, 0);
lean_dec(v_unused_3602_);
v___x_3596_ = v___x_3594_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_dec(v___x_3594_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 0, v_e_3376_);
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_e_3376_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v_e_3376_);
v_a_3603_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3594_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3594_);
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
}
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_e_3376_);
lean_dec_ref(v_below_3375_);
lean_dec_ref(v_containsRecFn_3374_);
lean_dec_ref(v_recFnNames_3373_);
lean_dec_ref(v_positions_3372_);
lean_dec_ref(v_recArgInfos_3371_);
v_a_3612_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3396_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3396_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
v___jp_3383_:
{
lean_object* v_dummy_3390_; lean_object* v_nargs_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
v_dummy_3390_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3391_ = l_Lean_Expr_getAppNumArgs(v_e_3384_);
lean_inc(v_nargs_3391_);
v___x_3392_ = lean_mk_array(v_nargs_3391_, v_dummy_3390_);
v___x_3393_ = lean_unsigned_to_nat(1u);
v___x_3394_ = lean_nat_sub(v_nargs_3391_, v___x_3393_);
lean_dec(v_nargs_3391_);
lean_inc_ref(v_e_3384_);
v___x_3395_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3371_, v_positions_3372_, v_recFnNames_3373_, v_containsRecFn_3374_, v_below_3375_, v_e_3384_, v_e_3384_, v___x_3392_, v___x_3394_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_);
lean_dec_ref(v___y_3388_);
return v___x_3395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3620_, lean_object* v_recArgInfos_3621_, lean_object* v_positions_3622_, lean_object* v_recFnNames_3623_, lean_object* v_containsRecFn_3624_, lean_object* v_below_3625_, lean_object* v_x_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = lean_expr_instantiate1(v_body_3620_, v_x_3626_);
lean_inc_ref(v___y_3630_);
v___x_3634_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3621_, v_positions_3622_, v_recFnNames_3623_, v_containsRecFn_3624_, v_below_3625_, v___x_3633_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3635_, lean_object* v_positions_3636_, lean_object* v_recFnNames_3637_, lean_object* v_containsRecFn_3638_, lean_object* v_below_3639_, lean_object* v_sz_3640_, lean_object* v_i_3641_, lean_object* v_bs_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
size_t v_sz_boxed_3649_; size_t v_i_boxed_3650_; lean_object* v_res_3651_; 
v_sz_boxed_3649_ = lean_unbox_usize(v_sz_3640_);
lean_dec(v_sz_3640_);
v_i_boxed_3650_ = lean_unbox_usize(v_i_3641_);
lean_dec(v_i_3641_);
v_res_3651_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3635_, v_positions_3636_, v_recFnNames_3637_, v_containsRecFn_3638_, v_below_3639_, v_sz_boxed_3649_, v_i_boxed_3650_, v_bs_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
lean_dec(v___y_3643_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3652_, lean_object* v_positions_3653_, lean_object* v_recFnNames_3654_, lean_object* v_containsRecFn_3655_, lean_object* v_a_3656_, lean_object* v_e_3657_, lean_object* v_as_3658_, lean_object* v_bs_3659_, lean_object* v_i_3660_, lean_object* v_cs_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
uint8_t v_a_28632__boxed_3668_; lean_object* v_res_3669_; 
v_a_28632__boxed_3668_ = lean_unbox(v_a_3656_);
v_res_3669_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3652_, v_positions_3653_, v_recFnNames_3654_, v_containsRecFn_3655_, v_a_28632__boxed_3668_, v_e_3657_, v_as_3658_, v_bs_3659_, v_i_3660_, v_cs_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v_bs_3659_);
lean_dec_ref(v_as_3658_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3670_, lean_object* v_positions_3671_, lean_object* v_recFnNames_3672_, lean_object* v_containsRecFn_3673_, lean_object* v_below_3674_, lean_object* v_e_3675_, lean_object* v_x_3676_, lean_object* v_x_3677_, lean_object* v_x_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3670_, v_positions_3671_, v_recFnNames_3672_, v_containsRecFn_3673_, v_below_3674_, v_e_3675_, v_x_3676_, v_x_3677_, v_x_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3686_, lean_object* v_positions_3687_, lean_object* v_recFnNames_3688_, lean_object* v_containsRecFn_3689_, lean_object* v_below_3690_, lean_object* v_e_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v_res_3698_; 
v_res_3698_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3686_, v_positions_3687_, v_recFnNames_3688_, v_containsRecFn_3689_, v_below_3690_, v_e_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
lean_dec(v_a_3696_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3699_, lean_object* v_msg_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3700_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3708_, lean_object* v_msg_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v_res_3716_; 
v_res_3716_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3708_, v_msg_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3717_, lean_object* v_name_3718_, lean_object* v_type_3719_, lean_object* v_val_3720_, lean_object* v_k_3721_, uint8_t v_nondep_3722_, uint8_t v_kind_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3718_, v_type_3719_, v_val_3720_, v_k_3721_, v_nondep_3722_, v_kind_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3731_, lean_object* v_name_3732_, lean_object* v_type_3733_, lean_object* v_val_3734_, lean_object* v_k_3735_, lean_object* v_nondep_3736_, lean_object* v_kind_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
uint8_t v_nondep_boxed_3744_; uint8_t v_kind_boxed_3745_; lean_object* v_res_3746_; 
v_nondep_boxed_3744_ = lean_unbox(v_nondep_3736_);
v_kind_boxed_3745_ = lean_unbox(v_kind_3737_);
v_res_3746_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3731_, v_name_3732_, v_type_3733_, v_val_3734_, v_k_3735_, v_nondep_boxed_3744_, v_kind_boxed_3745_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3747_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3763_, lean_object* v_msg_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3763_, v_msg_3764_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3772_, lean_object* v_msg_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3772_, v_msg_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec(v___y_3774_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3781_, lean_object* v_constName_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3790_, lean_object* v_constName_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
lean_object* v_res_3798_; 
v_res_3798_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3790_, v_constName_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3799_, lean_object* v_ref_3800_, lean_object* v_constName_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3800_, v_constName_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3809_, lean_object* v_ref_3810_, lean_object* v_constName_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3809_, v_ref_3810_, v_constName_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec(v_ref_3810_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3819_, lean_object* v_ref_3820_, lean_object* v_msg_3821_, lean_object* v_declHint_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3820_, v_msg_3821_, v_declHint_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3830_, lean_object* v_ref_3831_, lean_object* v_msg_3832_, lean_object* v_declHint_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3830_, v_ref_3831_, v_msg_3832_, v_declHint_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec(v_ref_3831_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3841_, lean_object* v_declHint_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3841_, v_declHint_3842_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3850_, lean_object* v_declHint_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3850_, v_declHint_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3859_, lean_object* v_ref_3860_, lean_object* v_msg_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3860_, v_msg_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3869_, lean_object* v_ref_3870_, lean_object* v_msg_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3869_, v_ref_3870_, v_msg_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec(v_ref_3870_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3879_, lean_object* v_e_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v_fst_3889_; lean_object* v_snd_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3887_ = lean_st_ref_take(v___y_3881_);
v___x_3888_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3879_, v_e_3880_, v___x_3887_);
v_fst_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_fst_3889_);
v_snd_3890_ = lean_ctor_get(v___x_3888_, 1);
lean_inc(v_snd_3890_);
lean_dec_ref(v___x_3888_);
v___x_3891_ = lean_st_ref_put(v___y_3881_, v_snd_3890_);
v___x_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3892_, 0, v_fst_3889_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3893_, lean_object* v_e_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3893_, v_e_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v_recFnNames_3893_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3902_, size_t v_i_3903_, lean_object* v_bs_3904_){
_start:
{
uint8_t v___x_3905_; 
v___x_3905_ = lean_usize_dec_lt(v_i_3903_, v_sz_3902_);
if (v___x_3905_ == 0)
{
return v_bs_3904_;
}
else
{
lean_object* v_v_3906_; lean_object* v_fnName_3907_; lean_object* v___x_3908_; lean_object* v_bs_x27_3909_; size_t v___x_3910_; size_t v___x_3911_; lean_object* v___x_3912_; 
v_v_3906_ = lean_array_uget_borrowed(v_bs_3904_, v_i_3903_);
v_fnName_3907_ = lean_ctor_get(v_v_3906_, 0);
lean_inc(v_fnName_3907_);
v___x_3908_ = lean_unsigned_to_nat(0u);
v_bs_x27_3909_ = lean_array_uset(v_bs_3904_, v_i_3903_, v___x_3908_);
v___x_3910_ = ((size_t)1ULL);
v___x_3911_ = lean_usize_add(v_i_3903_, v___x_3910_);
v___x_3912_ = lean_array_uset(v_bs_x27_3909_, v_i_3903_, v_fnName_3907_);
v_i_3903_ = v___x_3911_;
v_bs_3904_ = v___x_3912_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3914_, lean_object* v_i_3915_, lean_object* v_bs_3916_){
_start:
{
size_t v_sz_boxed_3917_; size_t v_i_boxed_3918_; lean_object* v_res_3919_; 
v_sz_boxed_3917_ = lean_unbox_usize(v_sz_3914_);
lean_dec(v_sz_3914_);
v_i_boxed_3918_ = lean_unbox_usize(v_i_3915_);
lean_dec(v_i_3915_);
v_res_3919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3917_, v_i_boxed_3918_, v_bs_3916_);
return v_res_3919_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = lean_unsigned_to_nat(16u);
v___x_3922_ = lean_mk_array(v___x_3921_, v___x_3920_);
return v___x_3922_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3924_ = lean_unsigned_to_nat(0u);
v___x_3925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
lean_ctor_set(v___x_3925_, 1, v___x_3923_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3926_, lean_object* v_positions_3927_, lean_object* v_below_3928_, lean_object* v_e_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_){
_start:
{
size_t v_sz_3935_; size_t v___x_3936_; lean_object* v_recFnNames_3937_; lean_object* v_containsRecFn_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_sz_3935_ = lean_array_size(v_recArgInfos_3926_);
v___x_3936_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3926_);
v_recFnNames_3937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3935_, v___x_3936_, v_recArgInfos_3926_);
lean_inc_ref(v_recFnNames_3937_);
v_containsRecFn_3938_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3938_, 0, v_recFnNames_3937_);
v___x_3939_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3940_ = lean_st_mk_ref(v___x_3939_);
lean_inc_ref(v_a_3932_);
v___x_3941_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3926_, v_positions_3927_, v_recFnNames_3937_, v_containsRecFn_3938_, v_below_3928_, v_e_3929_, v___x_3940_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3950_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3950_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_st_ref_get(v___x_3940_);
lean_dec(v___x_3940_);
lean_dec(v___x_3946_);
if (v_isShared_3945_ == 0)
{
v___x_3948_ = v___x_3944_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3942_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
else
{
lean_dec(v___x_3940_);
return v___x_3941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_3951_, lean_object* v_positions_3952_, lean_object* v_below_3953_, lean_object* v_e_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_3951_, v_positions_3952_, v_below_3953_, v_e_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
lean_dec(v_a_3958_);
lean_dec_ref(v_a_3957_);
lean_dec(v_a_3956_);
lean_dec_ref(v_a_3955_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_3961_, lean_object* v_k_3962_, uint8_t v_cleanupAnnotations_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v___f_3969_; uint8_t v___x_3970_; uint8_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___f_3969_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3969_, 0, v_k_3962_);
v___x_3970_ = 1;
v___x_3971_ = 0;
v___x_3972_ = lean_box(0);
v___x_3973_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3961_, v___x_3970_, v___x_3971_, v___x_3970_, v___x_3971_, v___x_3972_, v___f_3969_, v_cleanupAnnotations_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
v_a_3982_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3973_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3973_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_3990_, lean_object* v_k_3991_, lean_object* v_cleanupAnnotations_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3998_; lean_object* v_res_3999_; 
v_cleanupAnnotations_boxed_3998_ = lean_unbox(v_cleanupAnnotations_3992_);
v_res_3999_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_3990_, v_k_3991_, v_cleanupAnnotations_boxed_3998_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4000_, lean_object* v_e_4001_, lean_object* v_k_4002_, uint8_t v_cleanupAnnotations_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4001_, v_k_4002_, v_cleanupAnnotations_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4010_, lean_object* v_e_4011_, lean_object* v_k_4012_, lean_object* v_cleanupAnnotations_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4019_; lean_object* v_res_4020_; 
v_cleanupAnnotations_boxed_4019_ = lean_unbox(v_cleanupAnnotations_4013_);
v_res_4020_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4010_, v_e_4011_, v_k_4012_, v_cleanupAnnotations_boxed_4019_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4021_, lean_object* v_recArgInfo_4022_, lean_object* v_xs_4023_, lean_object* v___value_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; 
v___x_4030_ = l_Lean_Meta_instantiateForall(v_type_4021_, v_xs_4023_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4032_; lean_object* v_fst_4033_; lean_object* v_snd_4034_; uint8_t v___x_4035_; uint8_t v___x_4036_; uint8_t v___x_4037_; lean_object* v___x_4038_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v___x_4032_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4022_, v_xs_4023_);
v_fst_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_fst_4033_);
v_snd_4034_ = lean_ctor_get(v___x_4032_, 1);
lean_inc(v_snd_4034_);
lean_dec_ref(v___x_4032_);
v___x_4035_ = 0;
v___x_4036_ = 1;
v___x_4037_ = 1;
v___x_4038_ = l_Lean_Meta_mkForallFVars(v_snd_4034_, v_a_4031_, v___x_4035_, v___x_4036_, v___x_4036_, v___x_4037_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v_snd_4034_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v___x_4040_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref_known(v___x_4038_, 1);
v___x_4040_ = l_Lean_Meta_mkLambdaFVars(v_fst_4033_, v_a_4039_, v___x_4035_, v___x_4036_, v___x_4035_, v___x_4036_, v___x_4037_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v_fst_4033_);
return v___x_4040_;
}
else
{
lean_dec(v_fst_4033_);
return v___x_4038_;
}
}
else
{
lean_dec_ref(v_xs_4023_);
lean_dec_ref(v_recArgInfo_4022_);
return v___x_4030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4041_, lean_object* v_recArgInfo_4042_, lean_object* v_xs_4043_, lean_object* v___value_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4041_, v_recArgInfo_4042_, v_xs_4043_, v___value_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec_ref(v___value_4044_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4051_, lean_object* v_value_4052_, lean_object* v_type_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v___f_4059_; uint8_t v___x_4060_; lean_object* v___x_4061_; 
v___f_4059_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4059_, 0, v_type_4053_);
lean_closure_set(v___f_4059_, 1, v_recArgInfo_4051_);
v___x_4060_ = 0;
v___x_4061_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4052_, v___f_4059_, v___x_4060_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4062_, lean_object* v_value_4063_, lean_object* v_type_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4062_, v_value_4063_, v_type_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_a_4066_);
lean_dec_ref(v_a_4065_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v_recArgInfos_4071_, lean_object* v_positions_4072_, lean_object* v_value_4073_, lean_object* v_fst_4074_, lean_object* v_snd_4075_, lean_object* v_below_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v___x_4082_; 
lean_inc_ref(v_below_4076_);
v___x_4082_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4071_, v_positions_4072_, v_below_4076_, v_value_4073_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; uint8_t v___x_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4084_ = lean_unsigned_to_nat(1u);
v___x_4085_ = lean_mk_empty_array_with_capacity(v___x_4084_);
v___x_4086_ = lean_array_push(v___x_4085_, v_below_4076_);
v___x_4087_ = l_Array_append___redArg(v_fst_4074_, v___x_4086_);
lean_dec_ref(v___x_4086_);
v___x_4088_ = l_Array_append___redArg(v___x_4087_, v_snd_4075_);
v___x_4089_ = 0;
v___x_4090_ = 1;
v___x_4091_ = 1;
v___x_4092_ = l_Lean_Meta_mkLambdaFVars(v___x_4088_, v_a_4083_, v___x_4089_, v___x_4090_, v___x_4089_, v___x_4090_, v___x_4091_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec_ref(v___x_4088_);
return v___x_4092_;
}
else
{
lean_dec_ref(v_below_4076_);
lean_dec_ref(v_fst_4074_);
return v___x_4082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v_recArgInfos_4093_, lean_object* v_positions_4094_, lean_object* v_value_4095_, lean_object* v_fst_4096_, lean_object* v_snd_4097_, lean_object* v_below_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v_recArgInfos_4093_, v_positions_4094_, v_value_4095_, v_fst_4096_, v_snd_4097_, v_below_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec_ref(v_snd_4097_);
return v_res_4104_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4107_ = l_Lean_stringToMessageData(v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4108_, lean_object* v_recArgInfos_4109_, lean_object* v_positions_4110_, lean_object* v_FType_4111_, lean_object* v_xs_4112_, lean_object* v_value_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; lean_object* v_fst_4120_; lean_object* v_snd_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4140_; 
v___x_4119_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4108_, v_xs_4112_);
v_fst_4120_ = lean_ctor_get(v___x_4119_, 0);
v_snd_4121_ = lean_ctor_get(v___x_4119_, 1);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4123_ = v___x_4119_;
v_isShared_4124_ = v_isSharedCheck_4140_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_snd_4121_);
lean_inc(v_fst_4120_);
lean_dec(v___x_4119_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4140_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___f_4125_; lean_object* v___x_4126_; 
lean_inc(v_fst_4120_);
v___f_4125_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4125_, 0, v_recArgInfos_4109_);
lean_closure_set(v___f_4125_, 1, v_positions_4110_);
lean_closure_set(v___f_4125_, 2, v_value_4113_);
lean_closure_set(v___f_4125_, 3, v_fst_4120_);
lean_closure_set(v___f_4125_, 4, v_snd_4121_);
v___x_4126_ = l_Lean_Meta_instantiateForall(v_FType_4111_, v_fst_4120_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v_fst_4120_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4128_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc_n(v_a_4127_, 2);
lean_dec_ref_known(v___x_4126_, 1);
v___x_4128_ = l_Lean_Meta_whnfForall(v_a_4127_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
if (lean_obj_tag(v_a_4129_) == 7)
{
lean_object* v_binderName_4130_; lean_object* v_binderType_4131_; uint8_t v_binderInfo_4132_; lean_object* v___x_4133_; 
lean_dec(v_a_4127_);
lean_del_object(v___x_4123_);
v_binderName_4130_ = lean_ctor_get(v_a_4129_, 0);
lean_inc(v_binderName_4130_);
v_binderType_4131_ = lean_ctor_get(v_a_4129_, 1);
lean_inc_ref(v_binderType_4131_);
v_binderInfo_4132_ = lean_ctor_get_uint8(v_a_4129_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4129_, 3);
v___x_4133_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4130_, v_binderInfo_4132_, v_binderType_4131_, v___f_4125_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4133_;
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4137_; 
lean_dec(v_a_4129_);
lean_dec_ref(v___f_4125_);
v___x_4134_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1, &l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1);
v___x_4135_ = l_Lean_indentExpr(v_a_4127_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set_tag(v___x_4123_, 7);
lean_ctor_set(v___x_4123_, 1, v___x_4135_);
lean_ctor_set(v___x_4123_, 0, v___x_4134_);
v___x_4137_ = v___x_4123_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4134_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v___x_4135_);
v___x_4137_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4137_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4138_;
}
}
}
else
{
lean_dec(v_a_4127_);
lean_dec_ref(v___f_4125_);
lean_del_object(v___x_4123_);
return v___x_4128_;
}
}
else
{
lean_dec_ref(v___f_4125_);
lean_del_object(v___x_4123_);
return v___x_4126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4141_, lean_object* v_recArgInfos_4142_, lean_object* v_positions_4143_, lean_object* v_FType_4144_, lean_object* v_xs_4145_, lean_object* v_value_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4141_, v_recArgInfos_4142_, v_positions_4143_, v_FType_4144_, v_xs_4145_, v_value_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4153_, lean_object* v_positions_4154_, lean_object* v_recArgInfo_4155_, lean_object* v_value_4156_, lean_object* v_FType_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v___f_4163_; uint8_t v___x_4164_; lean_object* v___x_4165_; 
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4163_, 0, v_recArgInfo_4155_);
lean_closure_set(v___f_4163_, 1, v_recArgInfos_4153_);
lean_closure_set(v___f_4163_, 2, v_positions_4154_);
lean_closure_set(v___f_4163_, 3, v_FType_4157_);
v___x_4164_ = 0;
v___x_4165_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4156_, v___f_4163_, v___x_4164_, v_a_4158_, v_a_4159_, v_a_4160_, v_a_4161_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4166_, lean_object* v_positions_4167_, lean_object* v_recArgInfo_4168_, lean_object* v_value_4169_, lean_object* v_FType_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4166_, v_positions_4167_, v_recArgInfo_4168_, v_value_4169_, v_FType_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4177_, lean_object* v_params_4178_, uint8_t v_isIndPred_4179_, lean_object* v_brecOnUniv_4180_, lean_object* v_levels_4181_, lean_object* v_idx_4182_){
_start:
{
lean_object* v_n_4183_; lean_object* v___y_4185_; 
v_n_4183_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4177_, v_idx_4182_);
if (v_isIndPred_4179_ == 0)
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4188_, 0, v_brecOnUniv_4180_);
lean_ctor_set(v___x_4188_, 1, v_levels_4181_);
v___y_4185_ = v___x_4188_;
goto v___jp_4184_;
}
else
{
lean_dec(v_brecOnUniv_4180_);
v___y_4185_ = v_levels_4181_;
goto v___jp_4184_;
}
v___jp_4184_:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4186_ = l_Lean_Expr_const___override(v_n_4183_, v___y_4185_);
v___x_4187_ = l_Lean_mkAppN(v___x_4186_, v_params_4178_);
return v___x_4187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4189_, lean_object* v_params_4190_, lean_object* v_isIndPred_4191_, lean_object* v_brecOnUniv_4192_, lean_object* v_levels_4193_, lean_object* v_idx_4194_){
_start:
{
uint8_t v_isIndPred_boxed_4195_; lean_object* v_res_4196_; 
v_isIndPred_boxed_4195_ = lean_unbox(v_isIndPred_4191_);
v_res_4196_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4189_, v_params_4190_, v_isIndPred_boxed_4195_, v_brecOnUniv_4192_, v_levels_4193_, v_idx_4194_);
lean_dec(v_idx_4194_);
lean_dec_ref(v_params_4190_);
lean_dec_ref(v_toIndGroupInfo_4189_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4197_, lean_object* v_a_4198_, lean_object* v_n_4199_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_apply_1(v_brecOnCons_4197_, v_n_4199_);
v___x_4201_ = l_Lean_mkAppN(v___x_4200_, v_a_4198_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4202_, lean_object* v_a_4203_, lean_object* v_n_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4202_, v_a_4203_, v_n_4204_);
lean_dec_ref(v_a_4203_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4206_, lean_object* v_type_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_Lean_Meta_getLevel(v_type_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4214_, lean_object* v_type_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
lean_object* v_res_4221_; 
v_res_4221_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4214_, v_type_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec_ref(v_x_4214_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4222_, size_t v_sz_4223_, size_t v_i_4224_, lean_object* v_bs_4225_){
_start:
{
uint8_t v___x_4226_; 
v___x_4226_ = lean_usize_dec_lt(v_i_4224_, v_sz_4223_);
if (v___x_4226_ == 0)
{
return v_bs_4225_;
}
else
{
lean_object* v___x_4227_; lean_object* v_v_4228_; lean_object* v___x_4229_; lean_object* v_bs_x27_4230_; lean_object* v___x_4231_; size_t v___x_4232_; size_t v___x_4233_; lean_object* v___x_4234_; 
v___x_4227_ = l_Lean_instInhabitedExpr;
v_v_4228_ = lean_array_uget(v_bs_4225_, v_i_4224_);
v___x_4229_ = lean_unsigned_to_nat(0u);
v_bs_x27_4230_ = lean_array_uset(v_bs_4225_, v_i_4224_, v___x_4229_);
v___x_4231_ = lean_array_get_borrowed(v___x_4227_, v_xs_4222_, v_v_4228_);
lean_dec(v_v_4228_);
v___x_4232_ = ((size_t)1ULL);
v___x_4233_ = lean_usize_add(v_i_4224_, v___x_4232_);
lean_inc(v___x_4231_);
v___x_4234_ = lean_array_uset(v_bs_x27_4230_, v_i_4224_, v___x_4231_);
v_i_4224_ = v___x_4233_;
v_bs_4225_ = v___x_4234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4236_, lean_object* v_sz_4237_, lean_object* v_i_4238_, lean_object* v_bs_4239_){
_start:
{
size_t v_sz_boxed_4240_; size_t v_i_boxed_4241_; lean_object* v_res_4242_; 
v_sz_boxed_4240_ = lean_unbox_usize(v_sz_4237_);
lean_dec(v_sz_4237_);
v_i_boxed_4241_ = lean_unbox_usize(v_i_4238_);
lean_dec(v_i_4238_);
v_res_4242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4236_, v_sz_boxed_4240_, v_i_boxed_4241_, v_bs_4239_);
lean_dec_ref(v_xs_4236_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4243_, lean_object* v_f_4244_, lean_object* v_as_4245_, lean_object* v_bs_4246_, lean_object* v_i_4247_, lean_object* v_cs_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v___x_4254_; uint8_t v___x_4255_; 
v___x_4254_ = lean_array_get_size(v_as_4245_);
v___x_4255_ = lean_nat_dec_lt(v_i_4247_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4256_; 
lean_dec(v_i_4247_);
lean_dec_ref(v_f_4244_);
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v_cs_4248_);
return v___x_4256_;
}
else
{
lean_object* v___x_4257_; uint8_t v___x_4258_; 
v___x_4257_ = lean_array_get_size(v_bs_4246_);
v___x_4258_ = lean_nat_dec_lt(v_i_4247_, v___x_4257_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4259_; 
lean_dec(v_i_4247_);
lean_dec_ref(v_f_4244_);
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v_cs_4248_);
return v___x_4259_;
}
else
{
lean_object* v_a_4260_; lean_object* v_b_4261_; size_t v_sz_4262_; size_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v_a_4260_ = lean_array_fget_borrowed(v_as_4245_, v_i_4247_);
v_b_4261_ = lean_array_fget_borrowed(v_bs_4246_, v_i_4247_);
v_sz_4262_ = lean_array_size(v_b_4261_);
v___x_4263_ = ((size_t)0ULL);
lean_inc(v_b_4261_);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4243_, v_sz_4262_, v___x_4263_, v_b_4261_);
lean_inc_ref(v_f_4244_);
lean_inc(v___y_4252_);
lean_inc_ref(v___y_4251_);
lean_inc(v___y_4250_);
lean_inc_ref(v___y_4249_);
lean_inc(v_a_4260_);
v___x_4265_ = lean_apply_7(v_f_4244_, v_a_4260_, v___x_4264_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, lean_box(0));
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___x_4265_, 1);
v___x_4267_ = lean_unsigned_to_nat(1u);
v___x_4268_ = lean_nat_add(v_i_4247_, v___x_4267_);
lean_dec(v_i_4247_);
v___x_4269_ = lean_array_push(v_cs_4248_, v_a_4266_);
v_i_4247_ = v___x_4268_;
v_cs_4248_ = v___x_4269_;
goto _start;
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec_ref(v_cs_4248_);
lean_dec(v_i_4247_);
lean_dec_ref(v_f_4244_);
v_a_4271_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4265_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4265_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4279_, lean_object* v_f_4280_, lean_object* v_as_4281_, lean_object* v_bs_4282_, lean_object* v_i_4283_, lean_object* v_cs_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4279_, v_f_4280_, v_as_4281_, v_bs_4282_, v_i_4283_, v_cs_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec_ref(v_bs_4282_);
lean_dec_ref(v_as_4281_);
lean_dec_ref(v_xs_4279_);
return v_res_4290_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4291_; 
v___x_4291_ = l_Array_instInhabited___redArg();
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; lean_object* v_toApplicative_4299_; lean_object* v_toFunctor_4300_; lean_object* v_toSeq_4301_; lean_object* v_toSeqLeft_4302_; lean_object* v_toSeqRight_4303_; lean_object* v___f_4304_; lean_object* v___f_4305_; lean_object* v___f_4306_; lean_object* v___f_4307_; lean_object* v___x_4308_; lean_object* v___f_4309_; lean_object* v___f_4310_; lean_object* v___f_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v_toApplicative_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4346_; 
v___x_4298_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4299_ = lean_ctor_get(v___x_4298_, 0);
v_toFunctor_4300_ = lean_ctor_get(v_toApplicative_4299_, 0);
v_toSeq_4301_ = lean_ctor_get(v_toApplicative_4299_, 2);
v_toSeqLeft_4302_ = lean_ctor_get(v_toApplicative_4299_, 3);
v_toSeqRight_4303_ = lean_ctor_get(v_toApplicative_4299_, 4);
v___f_4304_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4300_, 2);
v___f_4306_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4306_, 0, v_toFunctor_4300_);
v___f_4307_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4307_, 0, v_toFunctor_4300_);
v___x_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___f_4306_);
lean_ctor_set(v___x_4308_, 1, v___f_4307_);
lean_inc(v_toSeqRight_4303_);
v___f_4309_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4309_, 0, v_toSeqRight_4303_);
lean_inc(v_toSeqLeft_4302_);
v___f_4310_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4310_, 0, v_toSeqLeft_4302_);
lean_inc(v_toSeq_4301_);
v___f_4311_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4311_, 0, v_toSeq_4301_);
v___x_4312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4308_);
lean_ctor_set(v___x_4312_, 1, v___f_4304_);
lean_ctor_set(v___x_4312_, 2, v___f_4311_);
lean_ctor_set(v___x_4312_, 3, v___f_4310_);
lean_ctor_set(v___x_4312_, 4, v___f_4309_);
v___x_4313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
lean_ctor_set(v___x_4313_, 1, v___f_4305_);
v___x_4314_ = l_StateRefT_x27_instMonad___redArg(v___x_4313_);
v_toApplicative_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4346_ == 0)
{
lean_object* v_unused_4347_; 
v_unused_4347_ = lean_ctor_get(v___x_4314_, 1);
lean_dec(v_unused_4347_);
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4346_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_toApplicative_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4346_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v_toFunctor_4319_; lean_object* v_toSeq_4320_; lean_object* v_toSeqLeft_4321_; lean_object* v_toSeqRight_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4344_; 
v_toFunctor_4319_ = lean_ctor_get(v_toApplicative_4315_, 0);
v_toSeq_4320_ = lean_ctor_get(v_toApplicative_4315_, 2);
v_toSeqLeft_4321_ = lean_ctor_get(v_toApplicative_4315_, 3);
v_toSeqRight_4322_ = lean_ctor_get(v_toApplicative_4315_, 4);
v_isSharedCheck_4344_ = !lean_is_exclusive(v_toApplicative_4315_);
if (v_isSharedCheck_4344_ == 0)
{
lean_object* v_unused_4345_; 
v_unused_4345_ = lean_ctor_get(v_toApplicative_4315_, 1);
lean_dec(v_unused_4345_);
v___x_4324_ = v_toApplicative_4315_;
v_isShared_4325_ = v_isSharedCheck_4344_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_toSeqRight_4322_);
lean_inc(v_toSeqLeft_4321_);
lean_inc(v_toSeq_4320_);
lean_inc(v_toFunctor_4319_);
lean_dec(v_toApplicative_4315_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4344_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___f_4326_; lean_object* v___f_4327_; lean_object* v___f_4328_; lean_object* v___f_4329_; lean_object* v___x_4330_; lean_object* v___f_4331_; lean_object* v___f_4332_; lean_object* v___f_4333_; lean_object* v___x_4335_; 
v___f_4326_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4319_);
v___f_4328_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4328_, 0, v_toFunctor_4319_);
v___f_4329_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4329_, 0, v_toFunctor_4319_);
v___x_4330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___f_4328_);
lean_ctor_set(v___x_4330_, 1, v___f_4329_);
v___f_4331_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4331_, 0, v_toSeqRight_4322_);
v___f_4332_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4332_, 0, v_toSeqLeft_4321_);
v___f_4333_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4333_, 0, v_toSeq_4320_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 4, v___f_4331_);
lean_ctor_set(v___x_4324_, 3, v___f_4332_);
lean_ctor_set(v___x_4324_, 2, v___f_4333_);
lean_ctor_set(v___x_4324_, 1, v___f_4326_);
lean_ctor_set(v___x_4324_, 0, v___x_4330_);
v___x_4335_ = v___x_4324_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4343_, 1, v___f_4326_);
lean_ctor_set(v_reuseFailAlloc_4343_, 2, v___f_4333_);
lean_ctor_set(v_reuseFailAlloc_4343_, 3, v___f_4332_);
lean_ctor_set(v_reuseFailAlloc_4343_, 4, v___f_4331_);
v___x_4335_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 1, v___f_4327_);
lean_ctor_set(v___x_4317_, 0, v___x_4335_);
v___x_4337_ = v___x_4317_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4342_, 1, v___f_4327_);
v___x_4337_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_855__overap_4340_; lean_object* v___x_4341_; 
v___x_4338_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4339_ = l_instInhabitedOfMonad___redArg(v___x_4337_, v___x_4338_);
v___x_855__overap_4340_ = lean_panic_fn_borrowed(v___x_4339_, v_msg_4292_);
lean_dec(v___x_4339_);
lean_inc(v___y_4296_);
lean_inc_ref(v___y_4295_);
lean_inc(v___y_4294_);
lean_inc_ref(v___y_4293_);
v___x_4341_ = lean_apply_5(v___x_855__overap_4340_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, lean_box(0));
return v___x_4341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
return v_res_4354_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4358_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4359_ = lean_unsigned_to_nat(2u);
v___x_4360_ = lean_unsigned_to_nat(73u);
v___x_4361_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4362_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4363_ = l_mkPanicMessageWithDecl(v___x_4362_, v___x_4361_, v___x_4360_, v___x_4359_, v___x_4358_);
return v___x_4363_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4365_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4366_ = lean_unsigned_to_nat(2u);
v___x_4367_ = lean_unsigned_to_nat(74u);
v___x_4368_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4369_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4370_ = l_mkPanicMessageWithDecl(v___x_4369_, v___x_4368_, v___x_4367_, v___x_4366_, v___x_4365_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4373_, lean_object* v_positions_4374_, lean_object* v_ys_4375_, lean_object* v_xs_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4382_ = lean_array_get_size(v_positions_4374_);
v___x_4383_ = lean_array_get_size(v_ys_4375_);
v___x_4384_ = lean_nat_dec_eq(v___x_4382_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_dec_ref(v_f_4373_);
v___x_4385_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4386_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4385_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
return v___x_4386_;
}
else
{
lean_object* v___x_4387_; lean_object* v___x_4388_; uint8_t v___x_4389_; 
v___x_4387_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4374_);
v___x_4388_ = lean_array_get_size(v_xs_4376_);
v___x_4389_ = lean_nat_dec_eq(v___x_4387_, v___x_4388_);
lean_dec(v___x_4387_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
lean_dec_ref(v_f_4373_);
v___x_4390_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4391_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4390_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
return v___x_4391_;
}
else
{
lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4392_ = lean_unsigned_to_nat(0u);
v___x_4393_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4394_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4376_, v_f_4373_, v_ys_4375_, v_positions_4374_, v___x_4392_, v___x_4393_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
return v___x_4394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4395_, lean_object* v_positions_4396_, lean_object* v_ys_4397_, lean_object* v_xs_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4395_, v_positions_4396_, v_ys_4397_, v_xs_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec_ref(v_xs_4398_);
lean_dec_ref(v_ys_4397_);
lean_dec_ref(v_positions_4396_);
return v_res_4404_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4406_ = lean_unsigned_to_nat(0u);
v___x_4407_ = l_Lean_Level_ofNat(v___x_4406_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4408_, lean_object* v_positions_4409_, lean_object* v_motives_4410_, uint8_t v_isIndPred_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v_indGroupInst_4420_; lean_object* v_brecOnUniv_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; 
v___x_4417_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4418_ = lean_unsigned_to_nat(0u);
v___x_4419_ = lean_array_get_borrowed(v___x_4417_, v_recArgInfos_4408_, v___x_4418_);
v_indGroupInst_4420_ = lean_ctor_get(v___x_4419_, 4);
if (v_isIndPred_4411_ == 0)
{
lean_object* v___f_4463_; lean_object* v___x_4464_; lean_object* v_motive_4465_; lean_object* v___x_4466_; 
v___f_4463_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4464_ = l_Lean_instInhabitedExpr;
v_motive_4465_ = lean_array_get_borrowed(v___x_4464_, v_motives_4410_, v___x_4418_);
lean_inc(v_motive_4465_);
v___x_4466_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4465_, v___f_4463_, v_isIndPred_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 1);
v_brecOnUniv_4422_ = v_a_4467_;
v___y_4423_ = v_a_4412_;
v___y_4424_ = v_a_4413_;
v___y_4425_ = v_a_4414_;
v___y_4426_ = v_a_4415_;
goto v___jp_4421_;
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
v_a_4468_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4466_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4466_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
else
{
lean_object* v___x_4476_; 
v___x_4476_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4422_ = v___x_4476_;
v___y_4423_ = v_a_4412_;
v___y_4424_ = v_a_4413_;
v___y_4425_ = v_a_4414_;
v___y_4426_ = v_a_4415_;
goto v___jp_4421_;
}
v___jp_4421_:
{
lean_object* v_toIndGroupInfo_4427_; lean_object* v_levels_4428_; lean_object* v_params_4429_; lean_object* v___x_4430_; lean_object* v_brecOnCons_4431_; lean_object* v_brecOnAux_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v_toIndGroupInfo_4427_ = lean_ctor_get(v_indGroupInst_4420_, 0);
v_levels_4428_ = lean_ctor_get(v_indGroupInst_4420_, 1);
v_params_4429_ = lean_ctor_get(v_indGroupInst_4420_, 2);
v___x_4430_ = lean_box(v_isIndPred_4411_);
lean_inc_n(v_levels_4428_, 2);
lean_inc(v_brecOnUniv_4422_);
lean_inc_ref(v_params_4429_);
lean_inc_ref(v_toIndGroupInfo_4427_);
v_brecOnCons_4431_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4431_, 0, v_toIndGroupInfo_4427_);
lean_closure_set(v_brecOnCons_4431_, 1, v_params_4429_);
lean_closure_set(v_brecOnCons_4431_, 2, v___x_4430_);
lean_closure_set(v_brecOnCons_4431_, 3, v_brecOnUniv_4422_);
lean_closure_set(v_brecOnCons_4431_, 4, v_levels_4428_);
v_brecOnAux_4432_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4427_, v_params_4429_, v_isIndPred_4411_, v_brecOnUniv_4422_, v_levels_4428_, v___x_4418_);
v___x_4433_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4427_);
v___x_4434_ = l_Lean_Meta_inferArgumentTypesN(v___x_4433_, v_brecOnAux_4432_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_object* v_a_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_a_4435_);
lean_dec_ref_known(v___x_4434_, 1);
v___x_4436_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4437_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4436_, v_positions_4409_, v_a_4435_, v_motives_4410_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v_a_4435_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4446_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4440_ = v___x_4437_;
v_isShared_4441_ = v_isSharedCheck_4446_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4437_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4446_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___f_4442_; lean_object* v___x_4444_; 
v___f_4442_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4442_, 0, v_brecOnCons_4431_);
lean_closure_set(v___f_4442_, 1, v_a_4438_);
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v___f_4442_);
v___x_4444_ = v___x_4440_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___f_4442_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec_ref(v_brecOnCons_4431_);
v_a_4447_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4437_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4437_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec_ref(v_brecOnCons_4431_);
v_a_4455_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4434_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4434_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4477_, lean_object* v_positions_4478_, lean_object* v_motives_4479_, lean_object* v_isIndPred_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_){
_start:
{
uint8_t v_isIndPred_boxed_4486_; lean_object* v_res_4487_; 
v_isIndPred_boxed_4486_ = lean_unbox(v_isIndPred_4480_);
v_res_4487_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4477_, v_positions_4478_, v_motives_4479_, v_isIndPred_boxed_4486_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
lean_dec(v_a_4482_);
lean_dec_ref(v_a_4481_);
lean_dec_ref(v_motives_4479_);
lean_dec_ref(v_positions_4478_);
lean_dec_ref(v_recArgInfos_4477_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4488_, lean_object* v_msg_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4496_, lean_object* v_msg_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4496_, v_msg_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4504_, lean_object* v_00_u03b1_4505_, lean_object* v_f_4506_, lean_object* v_positions_4507_, lean_object* v_ys_4508_, lean_object* v_xs_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4506_, v_positions_4507_, v_ys_4508_, v_xs_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4516_, lean_object* v_00_u03b1_4517_, lean_object* v_f_4518_, lean_object* v_positions_4519_, lean_object* v_ys_4520_, lean_object* v_xs_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4516_, v_00_u03b1_4517_, v_f_4518_, v_positions_4519_, v_ys_4520_, v_xs_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec_ref(v_xs_4521_);
lean_dec_ref(v_ys_4520_);
lean_dec_ref(v_positions_4519_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4528_, lean_object* v_00_u03b3_4529_, lean_object* v_xs_4530_, lean_object* v_f_4531_, lean_object* v_as_4532_, lean_object* v_bs_4533_, lean_object* v_i_4534_, lean_object* v_cs_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4530_, v_f_4531_, v_as_4532_, v_bs_4533_, v_i_4534_, v_cs_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4542_, lean_object* v_00_u03b3_4543_, lean_object* v_xs_4544_, lean_object* v_f_4545_, lean_object* v_as_4546_, lean_object* v_bs_4547_, lean_object* v_i_4548_, lean_object* v_cs_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4542_, v_00_u03b3_4543_, v_xs_4544_, v_f_4545_, v_as_4546_, v_bs_4547_, v_i_4548_, v_cs_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_bs_4547_);
lean_dec_ref(v_as_4546_);
lean_dec_ref(v_xs_4544_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(lean_object* v_type_4556_, lean_object* v_maxFVars_x3f_4557_, lean_object* v_k_4558_, uint8_t v_cleanupAnnotations_4559_, uint8_t v_whnfType_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___f_4566_; lean_object* v___x_4567_; 
v___f_4566_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4566_, 0, v_k_4558_);
v___x_4567_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4556_, v_maxFVars_x3f_4557_, v___f_4566_, v_cleanupAnnotations_4559_, v_whnfType_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4575_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4575_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4575_ == 0)
{
v___x_4570_ = v___x_4567_;
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4567_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4575_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4573_; 
if (v_isShared_4571_ == 0)
{
v___x_4573_ = v___x_4570_;
goto v_reusejp_4572_;
}
else
{
lean_object* v_reuseFailAlloc_4574_; 
v_reuseFailAlloc_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4574_, 0, v_a_4568_);
v___x_4573_ = v_reuseFailAlloc_4574_;
goto v_reusejp_4572_;
}
v_reusejp_4572_:
{
return v___x_4573_;
}
}
}
else
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
v_a_4576_ = lean_ctor_get(v___x_4567_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4567_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4567_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg___boxed(lean_object* v_type_4584_, lean_object* v_maxFVars_x3f_4585_, lean_object* v_k_4586_, lean_object* v_cleanupAnnotations_4587_, lean_object* v_whnfType_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4594_; uint8_t v_whnfType_boxed_4595_; lean_object* v_res_4596_; 
v_cleanupAnnotations_boxed_4594_ = lean_unbox(v_cleanupAnnotations_4587_);
v_whnfType_boxed_4595_ = lean_unbox(v_whnfType_4588_);
v_res_4596_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4584_, v_maxFVars_x3f_4585_, v_k_4586_, v_cleanupAnnotations_boxed_4594_, v_whnfType_boxed_4595_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_00_u03b1_4597_, lean_object* v_type_4598_, lean_object* v_maxFVars_x3f_4599_, lean_object* v_k_4600_, uint8_t v_cleanupAnnotations_4601_, uint8_t v_whnfType_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v___x_4608_; 
v___x_4608_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4598_, v_maxFVars_x3f_4599_, v_k_4600_, v_cleanupAnnotations_4601_, v_whnfType_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_);
return v___x_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_00_u03b1_4609_, lean_object* v_type_4610_, lean_object* v_maxFVars_x3f_4611_, lean_object* v_k_4612_, lean_object* v_cleanupAnnotations_4613_, lean_object* v_whnfType_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4620_; uint8_t v_whnfType_boxed_4621_; lean_object* v_res_4622_; 
v_cleanupAnnotations_boxed_4620_ = lean_unbox(v_cleanupAnnotations_4613_);
v_whnfType_boxed_4621_ = lean_unbox(v_whnfType_4614_);
v_res_4622_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_00_u03b1_4609_, v_type_4610_, v_maxFVars_x3f_4611_, v_k_4612_, v_cleanupAnnotations_boxed_4620_, v_whnfType_boxed_4621_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
return v_res_4622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v_numTypeFormers_4623_, lean_object* v_x_4624_, lean_object* v_brecOnType_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v___x_4631_; 
v___x_4631_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4623_, v_brecOnType_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_);
return v___x_4631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed(lean_object* v_numTypeFormers_4632_, lean_object* v_x_4633_, lean_object* v_brecOnType_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(v_numTypeFormers_4632_, v_x_4633_, v_brecOnType_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec_ref(v_x_4633_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v___x_4641_, lean_object* v_e_4642_){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = l_Lean_indentD(v_e_4642_);
v___x_4644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4641_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
return v___x_4644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4645_, lean_object* v_as_4646_, size_t v_sz_4647_, size_t v_i_4648_, lean_object* v_b_4649_){
_start:
{
uint8_t v___x_4651_; 
v___x_4651_ = lean_usize_dec_lt(v_i_4648_, v_sz_4647_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; 
lean_dec_ref(v_a_4645_);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_b_4649_);
return v___x_4652_;
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4654_; size_t v___x_4655_; size_t v___x_4656_; 
v_a_4653_ = lean_array_uget_borrowed(v_as_4646_, v_i_4648_);
lean_inc_ref(v_a_4645_);
v___x_4654_ = lean_array_set(v_b_4649_, v_a_4653_, v_a_4645_);
v___x_4655_ = ((size_t)1ULL);
v___x_4656_ = lean_usize_add(v_i_4648_, v___x_4655_);
v_i_4648_ = v___x_4656_;
v_b_4649_ = v___x_4654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4658_, lean_object* v_as_4659_, lean_object* v_sz_4660_, lean_object* v_i_4661_, lean_object* v_b_4662_, lean_object* v___y_4663_){
_start:
{
size_t v_sz_boxed_4664_; size_t v_i_boxed_4665_; lean_object* v_res_4666_; 
v_sz_boxed_4664_ = lean_unbox_usize(v_sz_4660_);
lean_dec(v_sz_4660_);
v_i_boxed_4665_ = lean_unbox_usize(v_i_4661_);
lean_dec(v_i_4661_);
v_res_4666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4658_, v_as_4659_, v_sz_boxed_4664_, v_i_boxed_4665_, v_b_4662_);
lean_dec_ref(v_as_4659_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(lean_object* v_as_4667_, size_t v_sz_4668_, size_t v_i_4669_, lean_object* v_b_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
uint8_t v___x_4676_; 
v___x_4676_ = lean_usize_dec_lt(v_i_4669_, v_sz_4668_);
if (v___x_4676_ == 0)
{
lean_object* v___x_4677_; 
v___x_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4677_, 0, v_b_4670_);
return v___x_4677_;
}
else
{
lean_object* v_snd_4678_; lean_object* v_fst_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4723_; 
v_snd_4678_ = lean_ctor_get(v_b_4670_, 1);
v_fst_4679_ = lean_ctor_get(v_b_4670_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v_b_4670_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4681_ = v_b_4670_;
v_isShared_4682_ = v_isSharedCheck_4723_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_snd_4678_);
lean_inc(v_fst_4679_);
lean_dec(v_b_4670_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4723_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v_array_4683_; lean_object* v_start_4684_; lean_object* v_stop_4685_; uint8_t v___x_4686_; 
v_array_4683_ = lean_ctor_get(v_snd_4678_, 0);
v_start_4684_ = lean_ctor_get(v_snd_4678_, 1);
v_stop_4685_ = lean_ctor_get(v_snd_4678_, 2);
v___x_4686_ = lean_nat_dec_lt(v_start_4684_, v_stop_4685_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4688_; 
if (v_isShared_4682_ == 0)
{
v___x_4688_ = v___x_4681_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_fst_4679_);
lean_ctor_set(v_reuseFailAlloc_4690_, 1, v_snd_4678_);
v___x_4688_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
lean_object* v___x_4689_; 
v___x_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
return v___x_4689_;
}
}
else
{
lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4719_; 
lean_inc(v_stop_4685_);
lean_inc(v_start_4684_);
lean_inc_ref(v_array_4683_);
v_isSharedCheck_4719_ = !lean_is_exclusive(v_snd_4678_);
if (v_isSharedCheck_4719_ == 0)
{
lean_object* v_unused_4720_; lean_object* v_unused_4721_; lean_object* v_unused_4722_; 
v_unused_4720_ = lean_ctor_get(v_snd_4678_, 2);
lean_dec(v_unused_4720_);
v_unused_4721_ = lean_ctor_get(v_snd_4678_, 1);
lean_dec(v_unused_4721_);
v_unused_4722_ = lean_ctor_get(v_snd_4678_, 0);
lean_dec(v_unused_4722_);
v___x_4692_ = v_snd_4678_;
v_isShared_4693_ = v_isSharedCheck_4719_;
goto v_resetjp_4691_;
}
else
{
lean_dec(v_snd_4678_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4719_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v_a_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4699_; 
v_a_4694_ = lean_array_uget_borrowed(v_as_4667_, v_i_4669_);
v___x_4695_ = lean_array_fget(v_array_4683_, v_start_4684_);
v___x_4696_ = lean_unsigned_to_nat(1u);
v___x_4697_ = lean_nat_add(v_start_4684_, v___x_4696_);
lean_dec(v_start_4684_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 1, v___x_4697_);
v___x_4699_ = v___x_4692_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_array_4683_);
lean_ctor_set(v_reuseFailAlloc_4718_, 1, v___x_4697_);
lean_ctor_set(v_reuseFailAlloc_4718_, 2, v_stop_4685_);
v___x_4699_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
size_t v_sz_4700_; size_t v___x_4701_; lean_object* v___x_4702_; 
v_sz_4700_ = lean_array_size(v___x_4695_);
v___x_4701_ = ((size_t)0ULL);
lean_inc(v_a_4694_);
v___x_4702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4694_, v___x_4695_, v_sz_4700_, v___x_4701_, v_fst_4679_);
lean_dec(v___x_4695_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4705_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref_known(v___x_4702_, 1);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 1, v___x_4699_);
lean_ctor_set(v___x_4681_, 0, v_a_4703_);
v___x_4705_ = v___x_4681_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
lean_ctor_set(v_reuseFailAlloc_4709_, 1, v___x_4699_);
v___x_4705_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
size_t v___x_4706_; size_t v___x_4707_; 
v___x_4706_ = ((size_t)1ULL);
v___x_4707_ = lean_usize_add(v_i_4669_, v___x_4706_);
v_i_4669_ = v___x_4707_;
v_b_4670_ = v___x_4705_;
goto _start;
}
}
else
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_dec_ref(v___x_4699_);
lean_del_object(v___x_4681_);
v_a_4710_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4702_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4702_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2___boxed(lean_object* v_as_4724_, lean_object* v_sz_4725_, lean_object* v_i_4726_, lean_object* v_b_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
size_t v_sz_boxed_4733_; size_t v_i_boxed_4734_; lean_object* v_res_4735_; 
v_sz_boxed_4733_ = lean_unbox_usize(v_sz_4725_);
lean_dec(v_sz_4725_);
v_i_boxed_4734_ = lean_unbox_usize(v_i_4726_);
lean_dec(v_i_4726_);
v_res_4735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_as_4724_, v_sz_boxed_4733_, v_i_boxed_4734_, v_b_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec_ref(v_as_4724_);
return v_res_4735_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4737_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4738_ = l_Lean_stringToMessageData(v___x_4737_);
return v___x_4738_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4739_; lean_object* v___f_4740_; 
v___x_4739_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4740_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1), 2, 1);
lean_closure_set(v___f_4740_, 0, v___x_4739_);
return v___f_4740_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4741_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4742_ = l_Lean_Expr_sort___override(v___x_4741_);
return v___x_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4743_, lean_object* v_positions_4744_, lean_object* v_brecOnConst_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_){
_start:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v_recArgInfo_4753_; lean_object* v_indicesPos_4754_; lean_object* v_indIdx_4755_; lean_object* v_numTypeFormers_4756_; lean_object* v___f_4757_; lean_object* v_brecOn_4758_; lean_object* v___f_4759_; uint8_t v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4751_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4752_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4753_ = lean_array_get_borrowed(v___x_4751_, v_recArgInfos_4743_, v___x_4752_);
v_indicesPos_4754_ = lean_ctor_get(v_recArgInfo_4753_, 3);
v_indIdx_4755_ = lean_ctor_get(v_recArgInfo_4753_, 5);
v_numTypeFormers_4756_ = lean_array_get_size(v_positions_4744_);
v___f_4757_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4757_, 0, v_numTypeFormers_4756_);
lean_inc(v_indIdx_4755_);
v_brecOn_4758_ = lean_apply_1(v_brecOnConst_4745_, v_indIdx_4755_);
v___f_4759_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4760_ = 0;
v___x_4761_ = lean_box(v___x_4760_);
lean_inc_ref(v_brecOn_4758_);
v___x_4762_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4762_, 0, v_brecOn_4758_);
lean_closure_set(v___x_4762_, 1, v___x_4761_);
v___x_4763_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4762_, v___f_4759_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v___x_4764_; 
lean_dec_ref_known(v___x_4763_, 1);
lean_inc(v_a_4749_);
lean_inc_ref(v_a_4748_);
lean_inc(v_a_4747_);
lean_inc_ref(v_a_4746_);
v___x_4764_ = lean_infer_type(v_brecOn_4758_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; uint8_t v___x_4770_; lean_object* v___x_4771_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4766_ = lean_array_get_size(v_indicesPos_4754_);
v___x_4767_ = lean_unsigned_to_nat(1u);
v___x_4768_ = lean_nat_add(v___x_4766_, v___x_4767_);
v___x_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4768_);
v___x_4770_ = 0;
v___x_4771_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_a_4765_, v___x_4769_, v___f_4757_, v___x_4770_, v___x_4770_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; size_t v_sz_4778_; size_t v___x_4779_; lean_object* v___x_4780_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_a_4772_);
lean_dec_ref_known(v___x_4771_, 1);
v___x_4773_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4744_);
v___x_4774_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4775_ = lean_mk_array(v___x_4773_, v___x_4774_);
v___x_4776_ = l_Array_toSubarray___redArg(v_positions_4744_, v___x_4752_, v_numTypeFormers_4756_);
v___x_4777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4775_);
lean_ctor_set(v___x_4777_, 1, v___x_4776_);
v_sz_4778_ = lean_array_size(v_a_4772_);
v___x_4779_ = ((size_t)0ULL);
v___x_4780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_a_4772_, v_sz_4778_, v___x_4779_, v___x_4777_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_);
lean_dec(v_a_4772_);
if (lean_obj_tag(v___x_4780_) == 0)
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4789_; 
v_a_4781_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4783_ = v___x_4780_;
v_isShared_4784_ = v_isSharedCheck_4789_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4780_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4789_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v_fst_4785_; lean_object* v___x_4787_; 
v_fst_4785_ = lean_ctor_get(v_a_4781_, 0);
lean_inc(v_fst_4785_);
lean_dec(v_a_4781_);
if (v_isShared_4784_ == 0)
{
lean_ctor_set(v___x_4783_, 0, v_fst_4785_);
v___x_4787_ = v___x_4783_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_fst_4785_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
v_a_4790_ = lean_ctor_get(v___x_4780_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4780_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4780_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4780_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4744_);
return v___x_4771_;
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec_ref(v___f_4757_);
lean_dec_ref(v_positions_4744_);
v_a_4798_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4764_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4764_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
else
{
lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4813_; 
lean_dec_ref(v_brecOn_4758_);
lean_dec_ref(v___f_4757_);
lean_dec_ref(v_positions_4744_);
v_a_4806_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4808_ = v___x_4763_;
v_isShared_4809_ = v_isSharedCheck_4813_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4763_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4814_, lean_object* v_positions_4815_, lean_object* v_brecOnConst_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4814_, v_positions_4815_, v_brecOnConst_4816_, v_a_4817_, v_a_4818_, v_a_4819_, v_a_4820_);
lean_dec(v_a_4820_);
lean_dec_ref(v_a_4819_);
lean_dec(v_a_4818_);
lean_dec_ref(v_a_4817_);
lean_dec_ref(v_recArgInfos_4814_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4823_, lean_object* v_as_4824_, size_t v_sz_4825_, size_t v_i_4826_, lean_object* v_b_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v___x_4833_; 
v___x_4833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4823_, v_as_4824_, v_sz_4825_, v_i_4826_, v_b_4827_);
return v___x_4833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4834_, lean_object* v_as_4835_, lean_object* v_sz_4836_, lean_object* v_i_4837_, lean_object* v_b_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
size_t v_sz_boxed_4844_; size_t v_i_boxed_4845_; lean_object* v_res_4846_; 
v_sz_boxed_4844_ = lean_unbox_usize(v_sz_4836_);
lean_dec(v_sz_4836_);
v_i_boxed_4845_ = lean_unbox_usize(v_i_4837_);
lean_dec(v_i_4837_);
v_res_4846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4834_, v_as_4835_, v_sz_boxed_4844_, v_i_boxed_4845_, v_b_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec_ref(v_as_4835_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4847_, lean_object* v_a_4848_){
_start:
{
if (lean_obj_tag(v_a_4847_) == 0)
{
lean_object* v___x_4849_; 
v___x_4849_ = l_List_reverse___redArg(v_a_4848_);
return v___x_4849_;
}
else
{
lean_object* v_head_4850_; lean_object* v_tail_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4862_; 
v_head_4850_ = lean_ctor_get(v_a_4847_, 0);
v_tail_4851_ = lean_ctor_get(v_a_4847_, 1);
v_isSharedCheck_4862_ = !lean_is_exclusive(v_a_4847_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4853_ = v_a_4847_;
v_isShared_4854_ = v_isSharedCheck_4862_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_tail_4851_);
lean_inc(v_head_4850_);
lean_dec(v_a_4847_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4862_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4859_; 
v___x_4855_ = l_Nat_reprFast(v_head_4850_);
v___x_4856_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
v___x_4857_ = l_Lean_MessageData_ofFormat(v___x_4856_);
if (v_isShared_4854_ == 0)
{
lean_ctor_set(v___x_4853_, 1, v_a_4848_);
lean_ctor_set(v___x_4853_, 0, v___x_4857_);
v___x_4859_ = v___x_4853_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4857_);
lean_ctor_set(v_reuseFailAlloc_4861_, 1, v_a_4848_);
v___x_4859_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
v_a_4847_ = v_tail_4851_;
v_a_4848_ = v___x_4859_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4863_, lean_object* v_a_4864_){
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
lean_object* v_head_4866_; lean_object* v_tail_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4879_; 
v_head_4866_ = lean_ctor_get(v_a_4863_, 0);
v_tail_4867_ = lean_ctor_get(v_a_4863_, 1);
v_isSharedCheck_4879_ = !lean_is_exclusive(v_a_4863_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4869_ = v_a_4863_;
v_isShared_4870_ = v_isSharedCheck_4879_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_tail_4867_);
lean_inc(v_head_4866_);
lean_dec(v_a_4863_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4879_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4871_ = lean_array_to_list(v_head_4866_);
v___x_4872_ = lean_box(0);
v___x_4873_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4871_, v___x_4872_);
v___x_4874_ = l_Lean_MessageData_ofList(v___x_4873_);
if (v_isShared_4870_ == 0)
{
lean_ctor_set(v___x_4869_, 1, v_a_4864_);
lean_ctor_set(v___x_4869_, 0, v___x_4874_);
v___x_4876_ = v___x_4869_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4874_);
lean_ctor_set(v_reuseFailAlloc_4878_, 1, v_a_4864_);
v___x_4876_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
v_a_4863_ = v_tail_4867_;
v_a_4864_ = v___x_4876_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4880_, lean_object* v_v_4881_, lean_object* v_i_4882_){
_start:
{
lean_object* v___x_4883_; uint8_t v___x_4884_; 
v___x_4883_ = lean_array_get_size(v_xs_4880_);
v___x_4884_ = lean_nat_dec_lt(v_i_4882_, v___x_4883_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; 
lean_dec(v_i_4882_);
v___x_4885_ = lean_box(0);
return v___x_4885_;
}
else
{
lean_object* v___x_4886_; uint8_t v___x_4887_; 
v___x_4886_ = lean_array_fget_borrowed(v_xs_4880_, v_i_4882_);
v___x_4887_ = lean_nat_dec_eq(v___x_4886_, v_v_4881_);
if (v___x_4887_ == 0)
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = lean_unsigned_to_nat(1u);
v___x_4889_ = lean_nat_add(v_i_4882_, v___x_4888_);
lean_dec(v_i_4882_);
v_i_4882_ = v___x_4889_;
goto _start;
}
else
{
lean_object* v___x_4891_; 
v___x_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4891_, 0, v_i_4882_);
return v___x_4891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4892_, lean_object* v_v_4893_, lean_object* v_i_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4892_, v_v_4893_, v_i_4894_);
lean_dec(v_v_4893_);
lean_dec_ref(v_xs_4892_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4896_, lean_object* v_v_4897_){
_start:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
v___x_4898_ = lean_unsigned_to_nat(0u);
v___x_4899_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4896_, v_v_4897_, v___x_4898_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4900_, lean_object* v_v_4901_){
_start:
{
lean_object* v_res_4902_; 
v_res_4902_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4900_, v_v_4901_);
lean_dec(v_v_4901_);
lean_dec_ref(v_xs_4900_);
return v_res_4902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4906_, lean_object* v_as_4907_, size_t v_sz_4908_, size_t v_i_4909_, lean_object* v_b_4910_){
_start:
{
uint8_t v___x_4911_; 
v___x_4911_ = lean_usize_dec_lt(v_i_4909_, v_sz_4908_);
if (v___x_4911_ == 0)
{
lean_inc_ref(v_b_4910_);
return v_b_4910_;
}
else
{
lean_object* v___x_4912_; lean_object* v_a_4913_; lean_object* v___x_4914_; 
v___x_4912_ = lean_box(0);
v_a_4913_ = lean_array_uget_borrowed(v_as_4907_, v_i_4909_);
v___x_4914_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4913_, v_fnIdx_4906_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v___x_4915_; size_t v___x_4916_; size_t v___x_4917_; 
v___x_4915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4916_ = ((size_t)1ULL);
v___x_4917_ = lean_usize_add(v_i_4909_, v___x_4916_);
v_i_4909_ = v___x_4917_;
v_b_4910_ = v___x_4915_;
goto _start;
}
else
{
lean_object* v_val_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4930_; 
v_val_4919_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4921_ = v___x_4914_;
v_isShared_4922_ = v_isSharedCheck_4930_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_val_4919_);
lean_dec(v___x_4914_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4930_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4926_; 
v___x_4923_ = lean_array_get_size(v_a_4913_);
v___x_4924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4924_, 0, v___x_4923_);
lean_ctor_set(v___x_4924_, 1, v_val_4919_);
if (v_isShared_4922_ == 0)
{
lean_ctor_set(v___x_4921_, 0, v___x_4924_);
v___x_4926_ = v___x_4921_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v___x_4924_);
v___x_4926_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
v___x_4928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
lean_ctor_set(v___x_4928_, 1, v___x_4912_);
return v___x_4928_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4931_, lean_object* v_as_4932_, lean_object* v_sz_4933_, lean_object* v_i_4934_, lean_object* v_b_4935_){
_start:
{
size_t v_sz_boxed_4936_; size_t v_i_boxed_4937_; lean_object* v_res_4938_; 
v_sz_boxed_4936_ = lean_unbox_usize(v_sz_4933_);
lean_dec(v_sz_4933_);
v_i_boxed_4937_ = lean_unbox_usize(v_i_4934_);
lean_dec(v_i_4934_);
v_res_4938_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4931_, v_as_4932_, v_sz_boxed_4936_, v_i_boxed_4937_, v_b_4935_);
lean_dec_ref(v_b_4935_);
lean_dec_ref(v_as_4932_);
lean_dec(v_fnIdx_4931_);
return v_res_4938_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; 
v___x_4940_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4941_ = l_Lean_stringToMessageData(v___x_4940_);
return v___x_4941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4942_, lean_object* v_positions_4943_, lean_object* v_fnIdx_4944_, lean_object* v_brecOnConst_4945_, lean_object* v_packedFArgs_4946_, lean_object* v_funTypes_4947_, lean_object* v_ys_4948_, lean_object* v___value_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v___x_4969_; lean_object* v_fst_4970_; lean_object* v_snd_4971_; lean_object* v___x_4972_; size_t v_sz_4973_; size_t v___x_4974_; lean_object* v___x_4975_; lean_object* v_fst_4976_; 
lean_inc_ref(v_ys_4948_);
lean_inc_ref(v_recArgInfo_4942_);
v___x_4969_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4942_, v_ys_4948_);
v_fst_4970_ = lean_ctor_get(v___x_4969_, 0);
lean_inc(v_fst_4970_);
v_snd_4971_ = lean_ctor_get(v___x_4969_, 1);
lean_inc(v_snd_4971_);
lean_dec_ref(v___x_4969_);
v___x_4972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_4973_ = lean_array_size(v_positions_4943_);
v___x_4974_ = ((size_t)0ULL);
v___x_4975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4944_, v_positions_4943_, v_sz_4973_, v___x_4974_, v___x_4972_);
v_fst_4976_ = lean_ctor_get(v___x_4975_, 0);
lean_inc(v_fst_4976_);
lean_dec_ref(v___x_4975_);
if (lean_obj_tag(v_fst_4976_) == 0)
{
lean_dec(v_snd_4971_);
lean_dec(v_fst_4970_);
lean_dec_ref(v_ys_4948_);
lean_dec_ref(v_brecOnConst_4945_);
lean_dec_ref(v_recArgInfo_4942_);
goto v___jp_4955_;
}
else
{
lean_object* v_val_4977_; 
v_val_4977_ = lean_ctor_get(v_fst_4976_, 0);
lean_inc(v_val_4977_);
lean_dec_ref_known(v_fst_4976_, 1);
if (lean_obj_tag(v_val_4977_) == 1)
{
lean_object* v_val_4978_; lean_object* v_fst_4979_; lean_object* v_snd_4980_; lean_object* v_indIdx_4981_; lean_object* v_brecOn_4982_; lean_object* v_brecOn_4983_; lean_object* v_brecOn_4984_; lean_object* v___x_4985_; 
lean_dec(v_fnIdx_4944_);
lean_dec_ref(v_positions_4943_);
v_val_4978_ = lean_ctor_get(v_val_4977_, 0);
lean_inc(v_val_4978_);
lean_dec_ref_known(v_val_4977_, 1);
v_fst_4979_ = lean_ctor_get(v_val_4978_, 0);
lean_inc(v_fst_4979_);
v_snd_4980_ = lean_ctor_get(v_val_4978_, 1);
lean_inc(v_snd_4980_);
lean_dec(v_val_4978_);
v_indIdx_4981_ = lean_ctor_get(v_recArgInfo_4942_, 5);
lean_inc(v_indIdx_4981_);
lean_dec_ref(v_recArgInfo_4942_);
v_brecOn_4982_ = lean_apply_1(v_brecOnConst_4945_, v_indIdx_4981_);
v_brecOn_4983_ = l_Lean_mkAppN(v_brecOn_4982_, v_fst_4970_);
lean_dec(v_fst_4970_);
v_brecOn_4984_ = l_Lean_mkAppN(v_brecOn_4983_, v_packedFArgs_4946_);
v___x_4985_ = l_Lean_Meta_PProdN_projM(v_fst_4979_, v_snd_4980_, v_brecOn_4984_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
lean_dec(v_snd_4980_);
lean_dec(v_fst_4979_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4987_; uint8_t v___x_4988_; uint8_t v___x_4989_; lean_object* v___x_4990_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___x_4985_, 1);
v___x_4987_ = l_Lean_mkAppN(v_a_4986_, v_snd_4971_);
lean_dec(v_snd_4971_);
v___x_4988_ = 1;
v___x_4989_ = 1;
v___x_4990_ = l_Lean_Meta_mkLetFVars(v_funTypes_4947_, v___x_4987_, v___x_4988_, v___x_4988_, v___x_4989_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; uint8_t v___x_4992_; lean_object* v___x_4993_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
lean_inc(v_a_4991_);
lean_dec_ref_known(v___x_4990_, 1);
v___x_4992_ = 0;
v___x_4993_ = l_Lean_Meta_mkLambdaFVars(v_ys_4948_, v_a_4991_, v___x_4992_, v___x_4988_, v___x_4992_, v___x_4988_, v___x_4989_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
lean_dec_ref(v_ys_4948_);
return v___x_4993_;
}
else
{
lean_dec_ref(v_ys_4948_);
return v___x_4990_;
}
}
else
{
lean_dec(v_snd_4971_);
lean_dec_ref(v_ys_4948_);
return v___x_4985_;
}
}
else
{
lean_dec(v_val_4977_);
lean_dec(v_snd_4971_);
lean_dec(v_fst_4970_);
lean_dec_ref(v_ys_4948_);
lean_dec_ref(v_brecOnConst_4945_);
lean_dec_ref(v_recArgInfo_4942_);
goto v___jp_4955_;
}
}
v___jp_4955_:
{
lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4956_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_4957_ = l_Nat_reprFast(v_fnIdx_4944_);
v___x_4958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
v___x_4959_ = l_Lean_MessageData_ofFormat(v___x_4958_);
v___x_4960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4960_, 0, v___x_4956_);
lean_ctor_set(v___x_4960_, 1, v___x_4959_);
v___x_4961_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_4962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4960_);
lean_ctor_set(v___x_4962_, 1, v___x_4961_);
v___x_4963_ = lean_array_to_list(v_positions_4943_);
v___x_4964_ = lean_box(0);
v___x_4965_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_4963_, v___x_4964_);
v___x_4966_ = l_Lean_MessageData_ofList(v___x_4965_);
v___x_4967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4962_);
lean_ctor_set(v___x_4967_, 1, v___x_4966_);
v___x_4968_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4967_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
return v___x_4968_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_4994_, lean_object* v_positions_4995_, lean_object* v_fnIdx_4996_, lean_object* v_brecOnConst_4997_, lean_object* v_packedFArgs_4998_, lean_object* v_funTypes_4999_, lean_object* v_ys_5000_, lean_object* v___value_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_4994_, v_positions_4995_, v_fnIdx_4996_, v_brecOnConst_4997_, v_packedFArgs_4998_, v_funTypes_4999_, v_ys_5000_, v___value_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec_ref(v___value_5001_);
lean_dec_ref(v_funTypes_4999_);
lean_dec_ref(v_packedFArgs_4998_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5008_, lean_object* v_fnIdx_5009_, lean_object* v_brecOnConst_5010_, lean_object* v_packedFArgs_5011_, lean_object* v_funTypes_5012_, lean_object* v_recArgInfo_5013_, lean_object* v_value_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_, lean_object* v_a_5017_, lean_object* v_a_5018_){
_start:
{
lean_object* v___f_5020_; uint8_t v___x_5021_; lean_object* v___x_5022_; 
v___f_5020_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5020_, 0, v_recArgInfo_5013_);
lean_closure_set(v___f_5020_, 1, v_positions_5008_);
lean_closure_set(v___f_5020_, 2, v_fnIdx_5009_);
lean_closure_set(v___f_5020_, 3, v_brecOnConst_5010_);
lean_closure_set(v___f_5020_, 4, v_packedFArgs_5011_);
lean_closure_set(v___f_5020_, 5, v_funTypes_5012_);
v___x_5021_ = 0;
v___x_5022_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5014_, v___f_5020_, v___x_5021_, v_a_5015_, v_a_5016_, v_a_5017_, v_a_5018_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5023_, lean_object* v_fnIdx_5024_, lean_object* v_brecOnConst_5025_, lean_object* v_packedFArgs_5026_, lean_object* v_funTypes_5027_, lean_object* v_recArgInfo_5028_, lean_object* v_value_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5023_, v_fnIdx_5024_, v_brecOnConst_5025_, v_packedFArgs_5026_, v_funTypes_5027_, v_recArgInfo_5028_, v_value_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
lean_dec(v_a_5031_);
lean_dec_ref(v_a_5030_);
return v_res_5035_;
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
