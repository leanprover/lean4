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
lean_dec_ref(v_fn_111_);
lean_dec_ref(v_a_110_);
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
lean_object* v_ref_358_; lean_object* v___x_359_; lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_405_; 
v_ref_358_ = lean_ctor_get(v___y_355_, 5);
v___x_359_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_);
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_405_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_405_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_405_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v_traceState_365_; lean_object* v_env_366_; lean_object* v_nextMacroScope_367_; lean_object* v_ngen_368_; lean_object* v_auxDeclNGen_369_; lean_object* v_cache_370_; lean_object* v_messages_371_; lean_object* v_infoState_372_; lean_object* v_snapshotTasks_373_; lean_object* v_newDecls_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_404_; 
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
v_newDecls_374_ = lean_ctor_get(v___x_364_, 9);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_404_ == 0)
{
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_404_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_newDecls_374_);
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
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_404_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
uint64_t v_tid_378_; lean_object* v_traces_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_403_; 
v_tid_378_ = lean_ctor_get_uint64(v_traceState_365_, sizeof(void*)*1);
v_traces_379_ = lean_ctor_get(v_traceState_365_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_traceState_365_);
if (v_isSharedCheck_403_ == 0)
{
v___x_381_ = v_traceState_365_;
v_isShared_382_ = v_isSharedCheck_403_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_traces_379_);
lean_dec(v_traceState_365_);
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
lean_ctor_set(v___x_387_, 0, v_cls_351_);
lean_ctor_set(v___x_387_, 1, v___x_383_);
lean_ctor_set(v___x_387_, 2, v___x_386_);
lean_ctor_set_float(v___x_387_, sizeof(void*)*3, v___x_384_);
lean_ctor_set_float(v___x_387_, sizeof(void*)*3 + 8, v___x_384_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*3 + 16, v___x_385_);
v___x_388_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_389_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v_a_360_);
lean_ctor_set(v___x_389_, 2, v___x_388_);
lean_inc(v_ref_358_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_ref_358_);
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
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_env_366_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_nextMacroScope_367_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_ngen_368_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_auxDeclNGen_369_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v___x_393_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v_cache_370_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_messages_371_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_infoState_372_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_snapshotTasks_373_);
lean_ctor_set(v_reuseFailAlloc_401_, 9, v_newDecls_374_);
v___x_395_ = v_reuseFailAlloc_401_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = lean_st_ref_set(v___y_356_, v___x_395_);
v___x_397_ = lean_box(0);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_397_);
v___x_399_ = v___x_362_;
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
lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___x_503_; 
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
v___x_503_ = lean_apply_5(v___f_420_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, lean_box(0));
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; uint8_t v___x_505_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = lean_unbox(v_a_504_);
lean_dec(v_a_504_);
if (v___x_505_ == 0)
{
v___y_465_ = v___y_426_;
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
v___y_468_ = v___y_429_;
goto v___jp_464_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_424_);
v___x_507_ = l_Lean_indentExpr(v_belowDict_424_);
v___x_508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
lean_inc(v_cls_423_);
v___x_509_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_423_, v___x_508_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_dec_ref(v___x_509_);
v___y_465_ = v___y_426_;
v___y_466_ = v___y_427_;
v___y_467_ = v___y_428_;
v___y_468_ = v___y_429_;
goto v___jp_464_;
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_423_);
lean_dec_ref(v_a_421_);
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_423_);
lean_dec_ref(v_a_421_);
v_a_518_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_503_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_503_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
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
lean_dec_ref(v_belowDict_424_);
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
v_options_482_ = lean_ctor_get(v___y_467_, 2);
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
lean_object* v_inheritedTraceOptions_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_inheritedTraceOptions_485_ = lean_ctor_get(v___y_467_, 13);
v___x_486_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_423_);
v___x_487_ = l_Lean_Name_append(v___x_486_, v_cls_423_);
v___x_488_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_485_, v_options_482_, v___x_487_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_423_);
v___x_489_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_491_ = l_Lean_indentExpr(v_belowDict_424_);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_423_, v___x_492_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; 
lean_dec_ref(v___x_493_);
v___x_494_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_494_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_495_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v___f_526_, lean_object* v_a_527_, lean_object* v_C_528_, lean_object* v_cls_529_, lean_object* v_belowDict_530_, lean_object* v_F_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v___f_526_, v_a_527_, v_C_528_, v_cls_529_, v_belowDict_530_, v_F_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec_ref(v_C_528_);
return v_res_537_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0(void){
_start:
{
lean_object* v___x_538_; lean_object* v_dummy_539_; 
v___x_538_ = lean_box(0);
v_dummy_539_ = l_Lean_Expr_sort___override(v___x_538_);
return v_dummy_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_540_, lean_object* v___f_541_, lean_object* v_C_542_, lean_object* v_cls_543_, lean_object* v_F_544_, lean_object* v_xs_545_, lean_object* v_belowDict_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v___x_552_; lean_object* v___x_553_; 
v___x_552_ = 1;
v___x_553_ = l_Lean_Meta_zetaReduce(v_arg_540_, v___x_552_, v___x_552_, v___x_552_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___f_555_; lean_object* v_dummy_556_; lean_object* v_nargs_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
lean_inc_n(v_a_554_, 2);
lean_dec_ref(v___x_553_);
v___f_555_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_555_, 0, v___f_541_);
lean_closure_set(v___f_555_, 1, v_a_554_);
lean_closure_set(v___f_555_, 2, v_C_542_);
lean_closure_set(v___f_555_, 3, v_cls_543_);
v_dummy_556_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_557_ = l_Lean_Expr_getAppNumArgs(v_a_554_);
lean_inc(v_nargs_557_);
v___x_558_ = lean_mk_array(v_nargs_557_, v_dummy_556_);
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_sub(v_nargs_557_, v___x_559_);
lean_dec(v_nargs_557_);
v___x_561_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_554_, v___x_558_, v___x_560_);
v___x_574_ = lean_array_get_size(v_xs_545_);
v___x_575_ = lean_array_get_size(v___x_561_);
v___x_576_ = lean_nat_dec_le(v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec_ref(v___x_561_);
lean_dec_ref(v___f_555_);
lean_dec_ref(v_F_544_);
v___x_577_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_547_, v___y_548_, v___y_549_, v___y_550_);
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
v___y_563_ = v___y_547_;
v___y_564_ = v___y_548_;
v___y_565_ = v___y_549_;
v___y_566_ = v___y_550_;
goto v___jp_562_;
}
v___jp_562_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_567_ = lean_array_get_size(v___x_561_);
v___x_568_ = lean_array_get_size(v_xs_545_);
v___x_569_ = lean_nat_sub(v___x_567_, v___x_568_);
v___x_570_ = l_Array_extract___redArg(v___x_561_, v___x_569_, v___x_567_);
lean_dec_ref(v___x_561_);
v___x_571_ = l_Lean_Expr_replaceFVars(v_belowDict_546_, v_xs_545_, v___x_570_);
v___x_572_ = l_Lean_mkAppN(v_F_544_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_573_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_571_, v___x_572_, v___f_555_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
return v___x_573_;
}
}
else
{
lean_dec_ref(v_F_544_);
lean_dec(v_cls_543_);
lean_dec_ref(v_C_542_);
lean_dec_ref(v___f_541_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_586_, lean_object* v___f_587_, lean_object* v_C_588_, lean_object* v_cls_589_, lean_object* v_F_590_, lean_object* v_xs_591_, lean_object* v_belowDict_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_586_, v___f_587_, v_C_588_, v_cls_589_, v_F_590_, v_xs_591_, v_belowDict_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v_belowDict_592_);
lean_dec_ref(v_xs_591_);
return v_res_598_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0));
v___x_601_ = l_Lean_stringToMessageData(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v___f_602_, lean_object* v_arg_603_, lean_object* v_C_604_, lean_object* v_cls_605_, lean_object* v_belowDict_606_, lean_object* v_F_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; 
lean_inc_ref(v___f_602_);
lean_inc(v___y_611_);
lean_inc_ref(v___y_610_);
lean_inc(v___y_609_);
lean_inc_ref(v___y_608_);
v___x_613_ = lean_apply_5(v___f_602_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, lean_box(0));
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___f_615_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; uint8_t v___x_623_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_a_614_);
lean_dec_ref(v___x_613_);
lean_inc(v_cls_605_);
v___f_615_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_615_, 0, v_arg_603_);
lean_closure_set(v___f_615_, 1, v___f_602_);
lean_closure_set(v___f_615_, 2, v_C_604_);
lean_closure_set(v___f_615_, 3, v_cls_605_);
lean_closure_set(v___f_615_, 4, v_F_607_);
v___x_623_ = lean_unbox(v_a_614_);
lean_dec(v_a_614_);
if (v___x_623_ == 0)
{
lean_dec(v_cls_605_);
v___y_617_ = v___y_608_;
v___y_618_ = v___y_609_;
v___y_619_ = v___y_610_;
v___y_620_ = v___y_611_;
goto v___jp_616_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_624_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_606_);
v___x_625_ = l_Lean_indentExpr(v_belowDict_606_);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_605_, v___x_626_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_dec_ref(v___x_627_);
v___y_617_ = v___y_608_;
v___y_618_ = v___y_609_;
v___y_619_ = v___y_610_;
v___y_620_ = v___y_611_;
goto v___jp_616_;
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v___f_615_);
lean_dec_ref(v_belowDict_606_);
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
v___jp_616_:
{
uint8_t v___x_621_; lean_object* v___x_622_; 
v___x_621_ = 0;
v___x_622_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_606_, v___f_615_, v___x_621_, v___x_621_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
return v___x_622_;
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v_F_607_);
lean_dec_ref(v_belowDict_606_);
lean_dec(v_cls_605_);
lean_dec_ref(v_C_604_);
lean_dec_ref(v_arg_603_);
lean_dec_ref(v___f_602_);
v_a_636_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_643_ == 0)
{
v___x_638_ = v___x_613_;
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_613_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_643_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_641_; 
if (v_isShared_639_ == 0)
{
v___x_641_ = v___x_638_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_636_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v___f_644_, lean_object* v_arg_645_, lean_object* v_C_646_, lean_object* v_cls_647_, lean_object* v_belowDict_648_, lean_object* v_F_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v___f_644_, v_arg_645_, v_C_646_, v_cls_647_, v_belowDict_648_, v_F_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_655_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_671_, lean_object* v_belowDict_672_, lean_object* v_arg_673_, lean_object* v_F_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_cls_680_; lean_object* v___f_681_; lean_object* v___x_682_; lean_object* v_a_683_; lean_object* v___f_684_; uint8_t v___x_685_; 
v_cls_680_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_681_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
v___x_682_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_680_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref(v___x_682_);
lean_inc_ref(v_arg_673_);
v___f_684_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_684_, 0, v___f_681_);
lean_closure_set(v___f_684_, 1, v_arg_673_);
lean_closure_set(v___f_684_, 2, v_C_671_);
lean_closure_set(v___f_684_, 3, v_cls_680_);
v___x_685_ = lean_unbox(v_a_683_);
lean_dec(v_a_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
lean_dec_ref(v_arg_673_);
v___x_686_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_672_, v_F_674_, v___f_684_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_687_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_672_);
v___x_688_ = l_Lean_indentExpr(v_belowDict_672_);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_689_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___x_692_ = l_Lean_indentExpr(v_arg_673_);
v___x_693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_680_, v___x_693_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v___x_695_; 
lean_dec_ref(v___x_694_);
v___x_695_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_672_, v_F_674_, v___f_684_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
return v___x_695_;
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec_ref(v___f_684_);
lean_dec_ref(v_F_674_);
lean_dec_ref(v_belowDict_672_);
v_a_696_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_694_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_704_, lean_object* v_belowDict_705_, lean_object* v_arg_706_, lean_object* v_F_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_704_, v_belowDict_705_, v_arg_706_, v_F_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v___x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_options_720_; uint8_t v_hasTrace_721_; 
v_options_720_ = lean_ctor_get(v___y_717_, 2);
v_hasTrace_721_ = lean_ctor_get_uint8(v_options_720_, sizeof(void*)*1);
if (v_hasTrace_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v___x_714_);
v___x_722_ = lean_box(v_hasTrace_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
else
{
lean_object* v_inheritedTraceOptions_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_inheritedTraceOptions_724_ = lean_ctor_get(v___y_717_, 13);
v___x_725_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_726_ = l_Lean_Name_append(v___x_725_, v___x_714_);
v___x_727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_724_, v_options_720_, v___x_726_);
lean_dec(v___x_726_);
v___x_728_ = lean_box(v___x_727_);
v___x_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
return v___x_729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v___x_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_737_, lean_object* v_x_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_744_, 0, v_t_737_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_745_, lean_object* v_x_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_745_, v_x_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec_ref(v_x_746_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v_t_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___closed__1));
v___x_763_ = l_Lean_Core_mkFreshUserName(v___x_762_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_773_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_773_ == 0)
{
v___x_766_ = v___x_763_;
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_763_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
v___f_768_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_768_, 0, v_t_756_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_a_764_);
lean_ctor_set(v___x_769_, 1, v___f_768_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_769_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v_t_756_);
v_a_774_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_763_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_763_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v_t_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v_t_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_789_, lean_object* v_a_790_, lean_object* v_x_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_798_ = lean_array_set(v___y_792_, v_a_790_, v___x_789_);
v___x_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_801_, lean_object* v_a_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_801_, v_a_802_, v_x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v_a_802_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_811_, lean_object* v_a_812_, lean_object* v_x_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_snd_820_; lean_object* v_fst_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_872_; 
v_snd_820_ = lean_ctor_get(v___y_814_, 1);
v_fst_821_ = lean_ctor_get(v___y_814_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___y_814_);
if (v_isSharedCheck_872_ == 0)
{
v___x_823_ = v___y_814_;
v_isShared_824_ = v_isSharedCheck_872_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_snd_820_);
lean_inc(v_fst_821_);
lean_dec(v___y_814_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_872_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_array_825_; lean_object* v_start_826_; lean_object* v_stop_827_; uint8_t v___x_828_; 
v_array_825_ = lean_ctor_get(v_snd_820_, 0);
v_start_826_ = lean_ctor_get(v_snd_820_, 1);
v_stop_827_ = lean_ctor_get(v_snd_820_, 2);
v___x_828_ = lean_nat_dec_lt(v_start_826_, v_stop_827_);
if (v___x_828_ == 0)
{
lean_object* v___x_830_; 
lean_dec_ref(v_a_812_);
lean_dec_ref(v___x_811_);
if (v_isShared_824_ == 0)
{
v___x_830_ = v___x_823_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_fst_821_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_snd_820_);
v___x_830_ = v_reuseFailAlloc_833_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
else
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_868_; 
lean_inc(v_stop_827_);
lean_inc(v_start_826_);
lean_inc_ref(v_array_825_);
v_isSharedCheck_868_ = !lean_is_exclusive(v_snd_820_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; 
v_unused_869_ = lean_ctor_get(v_snd_820_, 2);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_snd_820_, 1);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_snd_820_, 0);
lean_dec(v_unused_871_);
v___x_835_ = v_snd_820_;
v_isShared_836_ = v_isSharedCheck_868_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_snd_820_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_868_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___f_838_; size_t v_sz_839_; size_t v___x_840_; lean_object* v___x_8720__overap_841_; lean_object* v___x_842_; 
v___x_837_ = lean_array_fget_borrowed(v_array_825_, v_start_826_);
lean_inc(v___x_837_);
v___f_838_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_838_, 0, v___x_837_);
v_sz_839_ = lean_array_size(v_a_812_);
v___x_840_ = ((size_t)0ULL);
v___x_8720__overap_841_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_811_, v_a_812_, v___f_838_, v_sz_839_, v___x_840_, v_fst_821_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
lean_inc(v___y_816_);
lean_inc_ref(v___y_815_);
v___x_842_ = lean_apply_5(v___x_8720__overap_841_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, lean_box(0));
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_859_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_859_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_859_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_859_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_add(v_start_826_, v___x_847_);
lean_dec(v_start_826_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_848_);
v___x_850_ = v___x_835_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_array_825_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_848_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_stop_827_);
v___x_850_ = v_reuseFailAlloc_858_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_852_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_850_);
lean_ctor_set(v___x_823_, 0, v_a_843_);
v___x_852_ = v___x_823_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_843_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_857_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_853_);
v___x_855_ = v___x_845_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_del_object(v___x_835_);
lean_dec(v_stop_827_);
lean_dec(v_start_826_);
lean_dec_ref(v_array_825_);
lean_del_object(v___x_823_);
v_a_860_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_842_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_842_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_873_, lean_object* v_a_874_, lean_object* v_x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_873_, v_a_874_, v_x_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_882_;
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__8));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_positions_898_, lean_object* v_a_899_, lean_object* v___f_900_, lean_object* v___x_901_, lean_object* v___x_902_, lean_object* v_k_903_, lean_object* v___x_904_, lean_object* v___x_905_, lean_object* v___f_906_, lean_object* v___x_907_, lean_object* v_Cs_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v___x_8748__overap_915_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_908_);
lean_inc_ref(v___x_896_);
v___x_8748__overap_915_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_896_, v___x_897_, v___x_914_, v_positions_898_, v_a_899_, v_Cs_908_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
v___x_916_ = lean_apply_5(v___x_8748__overap_915_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref(v___x_916_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
v___x_918_ = lean_apply_5(v___f_900_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; uint8_t v___x_967_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref(v___x_918_);
v___x_920_ = l_Lean_mkAppN(v___x_901_, v_a_917_);
lean_dec(v_a_917_);
v___x_921_ = l_Subarray_copy___redArg(v___x_902_);
v___x_922_ = l_Lean_mkAppN(v___x_920_, v___x_921_);
lean_dec_ref(v___x_921_);
v___x_967_ = lean_unbox(v_a_919_);
lean_dec(v_a_919_);
if (v___x_967_ == 0)
{
v___y_924_ = v___y_909_;
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
v___y_927_ = v___y_912_;
goto v___jp_923_;
}
else
{
lean_object* v___f_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_toMonadRef_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_8810__overap_986_; lean_object* v___x_987_; 
v___f_968_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_970_ = l_Lean_Core_instMonadQuotationCoreM;
lean_inc(v___x_905_);
v___x_971_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_969_, v___x_905_, v___x_970_);
lean_inc(v___f_906_);
v___x_972_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_968_, v___f_906_, v___x_971_);
v_toMonadRef_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc_ref(v_toMonadRef_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_975_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6);
lean_inc_ref(v_Cs_908_);
v___x_976_ = lean_array_to_list(v_Cs_908_);
v___x_977_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7));
v___x_978_ = lean_box(0);
v___x_979_ = l_List_mapTR_loop___redArg(v___x_977_, v___x_976_, v___x_978_);
v___x_980_ = l_Lean_MessageData_ofList(v___x_979_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_975_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__9);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
lean_inc_ref(v___x_922_);
v___x_984_ = l_Lean_indentExpr(v___x_922_);
v___x_985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
lean_inc(v___x_904_);
lean_inc_ref(v___x_907_);
lean_inc_ref(v___x_896_);
v___x_8810__overap_986_ = l_Lean_addTrace___redArg(v___x_896_, v___x_907_, v_toMonadRef_973_, v___x_974_, v___x_904_, v___x_985_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
v___x_987_ = lean_apply_5(v___x_8810__overap_986_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, lean_box(0));
if (lean_obj_tag(v___x_987_) == 0)
{
lean_dec_ref(v___x_987_);
v___y_924_ = v___y_909_;
v___y_925_ = v___y_910_;
v___y_926_ = v___y_911_;
v___y_927_ = v___y_912_;
goto v___jp_923_;
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___x_922_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_896_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_987_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
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
lean_dec_ref(v___x_928_);
v___x_930_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
if (v___x_930_ == 0)
{
lean_object* v_options_931_; uint8_t v_hasTrace_932_; 
v_options_931_ = lean_ctor_get(v___y_926_, 2);
v_hasTrace_932_ = lean_ctor_get_uint8(v_options_931_, sizeof(void*)*1);
if (v_hasTrace_932_ == 0)
{
lean_object* v___x_933_; 
lean_dec_ref(v___x_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
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
lean_object* v_inheritedTraceOptions_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_inheritedTraceOptions_934_ = lean_ctor_get(v___y_926_, 13);
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_904_);
v___x_936_ = l_Lean_Name_append(v___x_935_, v___x_904_);
v___x_937_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_934_, v_options_931_, v___x_936_);
lean_dec(v___x_936_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_dec_ref(v___x_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v___x_896_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_938_ = lean_apply_7(v_k_903_, v_Cs_908_, v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_938_;
}
else
{
lean_object* v___f_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_toMonadRef_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_8780__overap_947_; lean_object* v___x_948_; 
v___f_939_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_940_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_941_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_942_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_940_, v___x_905_, v___x_941_);
v___x_943_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_939_, v___f_906_, v___x_942_);
v_toMonadRef_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc_ref(v_toMonadRef_944_);
lean_dec_ref(v___x_943_);
v___x_945_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_946_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
v___x_8780__overap_947_ = l_Lean_addTrace___redArg(v___x_896_, v___x_907_, v_toMonadRef_944_, v___x_945_, v___x_904_, v___x_946_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_948_ = lean_apply_5(v___x_8780__overap_947_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v___x_948_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_949_ = lean_apply_7(v_k_903_, v_Cs_908_, v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_949_;
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec_ref(v___x_922_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v_k_903_);
v_a_950_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
else
{
lean_object* v___x_958_; 
lean_dec_ref(v___x_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v___x_896_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
v___x_958_ = lean_apply_7(v_k_903_, v_Cs_908_, v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_958_;
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v___x_922_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_896_);
v_a_959_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_928_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_928_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_917_);
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_896_);
v_a_996_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_918_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_918_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_Cs_908_);
lean_dec_ref(v___x_907_);
lean_dec(v___f_906_);
lean_dec(v___x_905_);
lean_dec(v___x_904_);
lean_dec_ref(v_k_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v___f_900_);
lean_dec_ref(v___x_896_);
v_a_1004_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_916_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_916_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_1012_ = _args[0];
lean_object* v___x_1013_ = _args[1];
lean_object* v_positions_1014_ = _args[2];
lean_object* v_a_1015_ = _args[3];
lean_object* v___f_1016_ = _args[4];
lean_object* v___x_1017_ = _args[5];
lean_object* v___x_1018_ = _args[6];
lean_object* v_k_1019_ = _args[7];
lean_object* v___x_1020_ = _args[8];
lean_object* v___x_1021_ = _args[9];
lean_object* v___f_1022_ = _args[10];
lean_object* v___x_1023_ = _args[11];
lean_object* v_Cs_1024_ = _args[12];
lean_object* v___y_1025_ = _args[13];
lean_object* v___y_1026_ = _args[14];
lean_object* v___y_1027_ = _args[15];
lean_object* v___y_1028_ = _args[16];
lean_object* v___y_1029_ = _args[17];
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_1012_, v___x_1013_, v_positions_1014_, v_a_1015_, v___f_1016_, v___x_1017_, v___x_1018_, v_k_1019_, v___x_1020_, v___x_1021_, v___f_1022_, v___x_1023_, v_Cs_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1030_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(37u);
v___x_1032_ = l_Lean_Level_ofNat(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1034_ = l_Lean_Expr_sort___override(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1041_, lean_object* v___x_1042_, lean_object* v___f_1043_, lean_object* v___f_1044_, lean_object* v___x_1045_, lean_object* v_numTypeFormers_1046_, lean_object* v___f_1047_, lean_object* v___x_1048_, lean_object* v_k_1049_, lean_object* v___x_1050_, lean_object* v___x_1051_, lean_object* v___f_1052_, lean_object* v___x_1053_, lean_object* v_numIndParams_1054_, lean_object* v_a_1055_, lean_object* v_f_1056_, lean_object* v_args_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1196_ = lean_nat_add(v_numIndParams_1054_, v_numTypeFormers_1046_);
v___x_1197_ = lean_array_get_size(v_args_1057_);
v___x_1198_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
lean_dec(v___x_1196_);
if (v___x_1198_ == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v_args_1057_);
lean_dec_ref(v_f_1056_);
lean_dec(v_numIndParams_1054_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v___x_1048_);
lean_dec(v_numTypeFormers_1046_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___f_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v_positions_1041_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
v___x_1199_ = lean_apply_5(v___f_1047_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, lean_box(0));
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; uint8_t v___x_1201_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v___x_1199_);
v___x_1201_ = lean_unbox(v_a_1200_);
lean_dec(v_a_1200_);
if (v___x_1201_ == 0)
{
lean_dec_ref(v_a_1055_);
lean_dec_ref(v___x_1053_);
lean_dec(v___f_1052_);
lean_dec(v___x_1051_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1042_);
v___y_1183_ = v___y_1058_;
v___y_1184_ = v___y_1059_;
v___y_1185_ = v___y_1060_;
v___y_1186_ = v___y_1061_;
goto v___jp_1182_;
}
else
{
lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_toMonadRef_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_8955__overap_1212_; lean_object* v___x_1213_; 
v___f_1202_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_1203_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_1204_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1205_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1203_, v___x_1051_, v___x_1204_);
v___x_1206_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1202_, v___f_1052_, v___x_1205_);
v_toMonadRef_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_ref(v_toMonadRef_1207_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1209_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1210_ = l_Lean_indentExpr(v_a_1055_);
v___x_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_8955__overap_1212_ = l_Lean_addTrace___redArg(v___x_1042_, v___x_1053_, v_toMonadRef_1207_, v___x_1208_, v___x_1050_, v___x_1211_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
v___x_1213_ = lean_apply_5(v___x_8955__overap_1212_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, lean_box(0));
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_dec_ref(v___x_1213_);
v___y_1183_ = v___y_1058_;
v___y_1184_ = v___y_1059_;
v___y_1185_ = v___y_1060_;
v___y_1186_ = v___y_1061_;
goto v___jp_1182_;
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec_ref(v_a_1055_);
lean_dec_ref(v___x_1053_);
lean_dec(v___f_1052_);
lean_dec(v___x_1051_);
lean_dec(v___x_1050_);
lean_dec_ref(v___x_1042_);
v_a_1222_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1199_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1199_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_dec_ref(v_a_1055_);
v___y_1171_ = v___y_1058_;
v___y_1172_ = v___y_1059_;
v___y_1173_ = v___y_1060_;
v___y_1174_ = v___y_1061_;
goto v___jp_1170_;
}
v___jp_1063_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; size_t v_sz_1077_; size_t v___x_1078_; lean_object* v___x_8856__overap_1079_; lean_object* v___x_1080_; 
v___x_1072_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1073_ = lean_mk_array(v___y_1066_, v___x_1072_);
v___x_1074_ = lean_array_get_size(v___y_1064_);
v___x_1075_ = l_Array_toSubarray___redArg(v___y_1064_, v___y_1065_, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1073_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v_sz_1077_ = lean_array_size(v_positions_1041_);
v___x_1078_ = ((size_t)0ULL);
lean_inc_ref(v___x_1042_);
v___x_8856__overap_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1042_, v_positions_1041_, v___f_1043_, v_sz_1077_, v___x_1078_, v___x_1076_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
v___x_1080_ = lean_apply_5(v___x_8856__overap_1079_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, lean_box(0));
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v_fst_1082_; size_t v_sz_1083_; lean_object* v___x_8859__overap_1084_; lean_object* v___x_1085_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
v_fst_1082_ = lean_ctor_get(v_a_1081_, 0);
lean_inc(v_fst_1082_);
lean_dec(v_a_1081_);
v_sz_1083_ = lean_array_size(v_fst_1082_);
lean_inc_ref(v___x_1042_);
v___x_8859__overap_1084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1042_, v___f_1044_, v_sz_1083_, v___x_1078_, v_fst_1082_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
v___x_1085_ = lean_apply_5(v___x_8859__overap_1084_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, lean_box(0));
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; uint8_t v___x_1087_; lean_object* v___x_8863__overap_1088_; lean_object* v___x_1089_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref(v___x_1085_);
v___x_1087_ = 0;
v___x_8863__overap_1088_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1045_, v___x_1042_, v_a_1086_, v___y_1067_, v___x_1087_);
lean_inc(v___y_1071_);
lean_inc_ref(v___y_1070_);
lean_inc(v___y_1069_);
lean_inc_ref(v___y_1068_);
v___x_1089_ = lean_apply_5(v___x_8863__overap_1088_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, lean_box(0));
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec_ref(v___y_1067_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___x_1042_);
v_a_1090_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1085_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1085_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v___y_1067_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___f_1044_);
lean_dec_ref(v___x_1042_);
v_a_1098_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1080_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1080_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
v___jp_1106_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = l_Subarray_copy___redArg(v___y_1109_);
v___x_1115_ = l_Lean_mkAppN(v_f_1056_, v___x_1114_);
lean_dec_ref(v___x_1114_);
lean_inc_ref(v___x_1115_);
v___x_1116_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1046_, v___x_1115_, v___y_1111_, v___y_1110_, v___y_1107_, v___y_1112_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
lean_inc_ref(v___f_1047_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1107_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1111_);
v___x_1118_ = lean_apply_5(v___f_1047_, v___y_1111_, v___y_1110_, v___y_1107_, v___y_1112_, lean_box(0));
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v_lower_1120_; lean_object* v_upper_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1153_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v_lower_1120_ = lean_ctor_get(v___y_1113_, 0);
v_upper_1121_ = lean_ctor_get(v___y_1113_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___y_1113_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1123_ = v___y_1113_;
v_isShared_1124_ = v_isSharedCheck_1153_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_upper_1121_);
lean_inc(v_lower_1120_);
lean_dec(v___y_1113_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1153_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1125_ = l_Array_toSubarray___redArg(v_args_1057_, v_lower_1120_, v_upper_1121_);
lean_inc_ref(v___x_1053_);
lean_inc(v___f_1052_);
lean_inc(v___x_1051_);
lean_inc(v___x_1050_);
lean_inc(v_a_1117_);
lean_inc_ref(v_positions_1041_);
lean_inc_ref(v___x_1042_);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1126_, 0, v___x_1042_);
lean_closure_set(v___f_1126_, 1, v___x_1048_);
lean_closure_set(v___f_1126_, 2, v_positions_1041_);
lean_closure_set(v___f_1126_, 3, v_a_1117_);
lean_closure_set(v___f_1126_, 4, v___f_1047_);
lean_closure_set(v___f_1126_, 5, v___x_1115_);
lean_closure_set(v___f_1126_, 6, v___x_1125_);
lean_closure_set(v___f_1126_, 7, v_k_1049_);
lean_closure_set(v___f_1126_, 8, v___x_1050_);
lean_closure_set(v___f_1126_, 9, v___x_1051_);
lean_closure_set(v___f_1126_, 10, v___f_1052_);
lean_closure_set(v___f_1126_, 11, v___x_1053_);
v___x_1127_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1041_);
v___x_1128_ = lean_unbox(v_a_1119_);
lean_dec(v_a_1119_);
if (v___x_1128_ == 0)
{
lean_del_object(v___x_1123_);
lean_dec_ref(v___x_1053_);
lean_dec(v___f_1052_);
lean_dec(v___x_1051_);
lean_dec(v___x_1050_);
v___y_1064_ = v_a_1117_;
v___y_1065_ = v___y_1108_;
v___y_1066_ = v___x_1127_;
v___y_1067_ = v___f_1126_;
v___y_1068_ = v___y_1111_;
v___y_1069_ = v___y_1110_;
v___y_1070_ = v___y_1107_;
v___y_1071_ = v___y_1112_;
goto v___jp_1063_;
}
else
{
lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v_toMonadRef_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___f_1129_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_1130_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_1131_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1132_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1130_, v___x_1051_, v___x_1131_);
v___x_1133_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1129_, v___f_1052_, v___x_1132_);
v_toMonadRef_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc_ref(v_toMonadRef_1134_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1136_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1127_);
v___x_1137_ = l_Nat_reprFast(v___x_1127_);
v___x_1138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
v___x_1139_ = l_Lean_MessageData_ofFormat(v___x_1138_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set_tag(v___x_1123_, 7);
lean_ctor_set(v___x_1123_, 1, v___x_1139_);
lean_ctor_set(v___x_1123_, 0, v___x_1136_);
v___x_1141_ = v___x_1123_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_8902__overap_1142_; lean_object* v___x_1143_; 
lean_inc_ref(v___x_1042_);
v___x_8902__overap_1142_ = l_Lean_addTrace___redArg(v___x_1042_, v___x_1053_, v_toMonadRef_1134_, v___x_1135_, v___x_1050_, v___x_1141_);
lean_inc(v___y_1112_);
lean_inc_ref(v___y_1107_);
lean_inc(v___y_1110_);
lean_inc_ref(v___y_1111_);
v___x_1143_ = lean_apply_5(v___x_8902__overap_1142_, v___y_1111_, v___y_1110_, v___y_1107_, v___y_1112_, lean_box(0));
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_dec_ref(v___x_1143_);
v___y_1064_ = v_a_1117_;
v___y_1065_ = v___y_1108_;
v___y_1066_ = v___x_1127_;
v___y_1067_ = v___f_1126_;
v___y_1068_ = v___y_1111_;
v___y_1069_ = v___y_1110_;
v___y_1070_ = v___y_1107_;
v___y_1071_ = v___y_1112_;
goto v___jp_1063_;
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v___x_1127_);
lean_dec_ref(v___f_1126_);
lean_dec(v_a_1117_);
lean_dec(v___y_1108_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___f_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_positions_1041_);
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v_a_1117_);
lean_dec_ref(v___x_1115_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1108_);
lean_dec_ref(v_args_1057_);
lean_dec_ref(v___x_1053_);
lean_dec(v___f_1052_);
lean_dec(v___x_1051_);
lean_dec(v___x_1050_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v___f_1047_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___f_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_positions_1041_);
v_a_1154_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1118_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1118_);
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
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v___x_1115_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1108_);
lean_dec_ref(v_args_1057_);
lean_dec_ref(v___x_1053_);
lean_dec(v___f_1052_);
lean_dec(v___x_1051_);
lean_dec(v___x_1050_);
lean_dec_ref(v_k_1049_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v___f_1047_);
lean_dec_ref(v___x_1045_);
lean_dec_ref(v___f_1044_);
lean_dec_ref(v___f_1043_);
lean_dec_ref(v___x_1042_);
lean_dec_ref(v_positions_1041_);
v_a_1162_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1116_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1116_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
v___jp_1170_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1054_);
lean_inc_ref(v_args_1057_);
v___x_1176_ = l_Array_toSubarray___redArg(v_args_1057_, v___x_1175_, v_numIndParams_1054_);
v___x_1177_ = lean_nat_add(v_numIndParams_1054_, v_numTypeFormers_1046_);
lean_dec(v_numIndParams_1054_);
v___x_1178_ = lean_array_get_size(v_args_1057_);
v___x_1179_ = lean_nat_dec_le(v___x_1177_, v___x_1175_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1177_);
lean_ctor_set(v___x_1180_, 1, v___x_1178_);
v___y_1107_ = v___y_1173_;
v___y_1108_ = v___x_1175_;
v___y_1109_ = v___x_1176_;
v___y_1110_ = v___y_1172_;
v___y_1111_ = v___y_1171_;
v___y_1112_ = v___y_1174_;
v___y_1113_ = v___x_1180_;
goto v___jp_1106_;
}
else
{
lean_object* v___x_1181_; 
lean_dec(v___x_1177_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1175_);
lean_ctor_set(v___x_1181_, 1, v___x_1178_);
v___y_1107_ = v___y_1173_;
v___y_1108_ = v___x_1175_;
v___y_1109_ = v___x_1176_;
v___y_1110_ = v___y_1172_;
v___y_1111_ = v___y_1171_;
v___y_1112_ = v___y_1174_;
v___y_1113_ = v___x_1181_;
goto v___jp_1106_;
}
}
v___jp_1182_:
{
lean_object* v___x_1187_; lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
v___x_1187_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1230_ = _args[0];
lean_object* v___x_1231_ = _args[1];
lean_object* v___f_1232_ = _args[2];
lean_object* v___f_1233_ = _args[3];
lean_object* v___x_1234_ = _args[4];
lean_object* v_numTypeFormers_1235_ = _args[5];
lean_object* v___f_1236_ = _args[6];
lean_object* v___x_1237_ = _args[7];
lean_object* v_k_1238_ = _args[8];
lean_object* v___x_1239_ = _args[9];
lean_object* v___x_1240_ = _args[10];
lean_object* v___f_1241_ = _args[11];
lean_object* v___x_1242_ = _args[12];
lean_object* v_numIndParams_1243_ = _args[13];
lean_object* v_a_1244_ = _args[14];
lean_object* v_f_1245_ = _args[15];
lean_object* v_args_1246_ = _args[16];
lean_object* v___y_1247_ = _args[17];
lean_object* v___y_1248_ = _args[18];
lean_object* v___y_1249_ = _args[19];
lean_object* v___y_1250_ = _args[20];
lean_object* v___y_1251_ = _args[21];
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1230_, v___x_1231_, v___f_1232_, v___f_1233_, v___x_1234_, v_numTypeFormers_1235_, v___f_1236_, v___x_1237_, v_k_1238_, v___x_1239_, v___x_1240_, v___f_1241_, v___x_1242_, v_numIndParams_1243_, v_a_1244_, v_f_1245_, v_args_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
return v_res_1252_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_instMonadEIO(lean_box(0));
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1255_ = l_StateRefT_x27_instMonad___redArg(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1264_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1263_, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1266_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1267_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1271_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1272_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1273_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2));
v___x_1274_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1273_, v___x_1272_, v___x_1271_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___f_1276_; lean_object* v___f_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1276_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1277_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_1278_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1277_, v___f_1276_, v___x_1275_);
return v___x_1278_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1282_, lean_object* v_numIndParams_1283_, lean_object* v_positions_1284_, lean_object* v_k_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v_toApplicative_1292_; lean_object* v_toFunctor_1293_; lean_object* v_toSeq_1294_; lean_object* v_toSeqLeft_1295_; lean_object* v_toSeqRight_1296_; lean_object* v___f_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___f_1300_; lean_object* v___x_1301_; lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_toApplicative_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1435_; 
v___x_1291_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1292_ = lean_ctor_get(v___x_1291_, 0);
v_toFunctor_1293_ = lean_ctor_get(v_toApplicative_1292_, 0);
v_toSeq_1294_ = lean_ctor_get(v_toApplicative_1292_, 2);
v_toSeqLeft_1295_ = lean_ctor_get(v_toApplicative_1292_, 3);
v_toSeqRight_1296_ = lean_ctor_get(v_toApplicative_1292_, 4);
v___f_1297_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1293_, 2);
v___f_1299_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1299_, 0, v_toFunctor_1293_);
v___f_1300_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1300_, 0, v_toFunctor_1293_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___f_1299_);
lean_ctor_set(v___x_1301_, 1, v___f_1300_);
lean_inc(v_toSeqRight_1296_);
v___f_1302_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1302_, 0, v_toSeqRight_1296_);
lean_inc(v_toSeqLeft_1295_);
v___f_1303_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1303_, 0, v_toSeqLeft_1295_);
lean_inc(v_toSeq_1294_);
v___f_1304_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1304_, 0, v_toSeq_1294_);
v___x_1305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1301_);
lean_ctor_set(v___x_1305_, 1, v___f_1297_);
lean_ctor_set(v___x_1305_, 2, v___f_1304_);
lean_ctor_set(v___x_1305_, 3, v___f_1303_);
lean_ctor_set(v___x_1305_, 4, v___f_1302_);
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___f_1298_);
v___x_1307_ = l_StateRefT_x27_instMonad___redArg(v___x_1306_);
v_toApplicative_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1435_ == 0)
{
lean_object* v_unused_1436_; 
v_unused_1436_ = lean_ctor_get(v___x_1307_, 1);
lean_dec(v_unused_1436_);
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1435_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_toApplicative_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1435_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_toFunctor_1312_; lean_object* v_toSeq_1313_; lean_object* v_toSeqLeft_1314_; lean_object* v_toSeqRight_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1433_; 
v_toFunctor_1312_ = lean_ctor_get(v_toApplicative_1308_, 0);
v_toSeq_1313_ = lean_ctor_get(v_toApplicative_1308_, 2);
v_toSeqLeft_1314_ = lean_ctor_get(v_toApplicative_1308_, 3);
v_toSeqRight_1315_ = lean_ctor_get(v_toApplicative_1308_, 4);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_toApplicative_1308_);
if (v_isSharedCheck_1433_ == 0)
{
lean_object* v_unused_1434_; 
v_unused_1434_ = lean_ctor_get(v_toApplicative_1308_, 1);
lean_dec(v_unused_1434_);
v___x_1317_ = v_toApplicative_1308_;
v_isShared_1318_ = v_isSharedCheck_1433_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_toSeqRight_1315_);
lean_inc(v_toSeqLeft_1314_);
lean_inc(v_toSeq_1313_);
lean_inc(v_toFunctor_1312_);
lean_dec(v_toApplicative_1308_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1433_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___f_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___x_1328_; 
v___f_1319_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1320_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1312_);
v___f_1321_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1321_, 0, v_toFunctor_1312_);
v___f_1322_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1322_, 0, v_toFunctor_1312_);
v___x_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___f_1321_);
lean_ctor_set(v___x_1323_, 1, v___f_1322_);
v___f_1324_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1324_, 0, v_toSeqRight_1315_);
v___f_1325_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1325_, 0, v_toSeqLeft_1314_);
v___f_1326_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1326_, 0, v_toSeq_1313_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v___f_1324_);
lean_ctor_set(v___x_1317_, 3, v___f_1325_);
lean_ctor_set(v___x_1317_, 2, v___f_1326_);
lean_ctor_set(v___x_1317_, 1, v___f_1319_);
lean_ctor_set(v___x_1317_, 0, v___x_1323_);
v___x_1328_ = v___x_1317_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___f_1319_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v___f_1326_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v___f_1325_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v___f_1324_);
v___x_1328_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 1, v___f_1320_);
lean_ctor_set(v___x_1310_, 0, v___x_1328_);
v___x_1330_ = v___x_1310_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___f_1320_);
v___x_1330_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___f_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_toApplicative_1334_; lean_object* v_toFunctor_1335_; lean_object* v_toSeq_1336_; lean_object* v_toSeqLeft_1337_; lean_object* v_toSeqRight_1338_; lean_object* v___f_1339_; lean_object* v___f_1340_; lean_object* v___x_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___f_1331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1332_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1333_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1334_ = lean_ctor_get(v___x_1291_, 0);
v_toFunctor_1335_ = lean_ctor_get(v_toApplicative_1334_, 0);
v_toSeq_1336_ = lean_ctor_get(v_toApplicative_1334_, 2);
v_toSeqLeft_1337_ = lean_ctor_get(v_toApplicative_1334_, 3);
v_toSeqRight_1338_ = lean_ctor_get(v_toApplicative_1334_, 4);
lean_inc_ref_n(v_toFunctor_1335_, 2);
v___f_1339_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1339_, 0, v_toFunctor_1335_);
v___f_1340_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1340_, 0, v_toFunctor_1335_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___f_1339_);
lean_ctor_set(v___x_1341_, 1, v___f_1340_);
lean_inc(v_toSeqRight_1338_);
v___f_1342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1342_, 0, v_toSeqRight_1338_);
lean_inc(v_toSeqLeft_1337_);
v___f_1343_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1343_, 0, v_toSeqLeft_1337_);
lean_inc(v_toSeq_1336_);
v___f_1344_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1344_, 0, v_toSeq_1336_);
v___x_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1341_);
lean_ctor_set(v___x_1345_, 1, v___f_1297_);
lean_ctor_set(v___x_1345_, 2, v___f_1344_);
lean_ctor_set(v___x_1345_, 3, v___f_1343_);
lean_ctor_set(v___x_1345_, 4, v___f_1342_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v___f_1298_);
v___x_1347_ = l_StateRefT_x27_instMonad___redArg(v___x_1346_);
v___x_1348_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1348_, 0, lean_box(0));
lean_closure_set(v___x_1348_, 1, lean_box(0));
lean_closure_set(v___x_1348_, 2, v___x_1347_);
v___x_1349_ = l_instMonadControlTOfPure___redArg(v___x_1348_);
lean_inc(v_a_1289_);
lean_inc_ref(v_a_1288_);
lean_inc(v_a_1287_);
lean_inc_ref(v_a_1286_);
lean_inc_ref(v_below_1282_);
v___x_1350_ = lean_infer_type(v_below_1282_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___f_1353_; lean_object* v___x_1354_; lean_object* v_a_1355_; lean_object* v___f_1356_; lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v_numTypeFormers_1359_; lean_object* v___f_1360_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v___x_1406_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc_n(v_a_1351_, 2);
lean_dec_ref(v___x_1350_);
v___x_1352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1353_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1354_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1352_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1354_);
v___f_1356_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
lean_inc_ref_n(v___x_1330_, 2);
v___f_1357_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed), 9, 1);
lean_closure_set(v___f_1357_, 0, v___x_1330_);
v___x_1358_ = l_Lean_instInhabitedExpr;
v_numTypeFormers_1359_ = lean_array_get_size(v_positions_1284_);
v___f_1360_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1360_, 0, v_positions_1284_);
lean_closure_set(v___f_1360_, 1, v___x_1330_);
lean_closure_set(v___f_1360_, 2, v___f_1357_);
lean_closure_set(v___f_1360_, 3, v___f_1356_);
lean_closure_set(v___f_1360_, 4, v___x_1349_);
lean_closure_set(v___f_1360_, 5, v_numTypeFormers_1359_);
lean_closure_set(v___f_1360_, 6, v___f_1353_);
lean_closure_set(v___f_1360_, 7, v___x_1358_);
lean_closure_set(v___f_1360_, 8, v_k_1285_);
lean_closure_set(v___f_1360_, 9, v___x_1352_);
lean_closure_set(v___f_1360_, 10, v___x_1332_);
lean_closure_set(v___f_1360_, 11, v___f_1331_);
lean_closure_set(v___f_1360_, 12, v___x_1333_);
lean_closure_set(v___f_1360_, 13, v_numIndParams_1283_);
lean_closure_set(v___f_1360_, 14, v_a_1351_);
v___x_1406_ = lean_unbox(v_a_1355_);
lean_dec(v_a_1355_);
if (v___x_1406_ == 0)
{
v___y_1374_ = v_a_1286_;
v___y_1375_ = v_a_1287_;
v___y_1376_ = v_a_1288_;
v___y_1377_ = v_a_1289_;
goto v___jp_1373_;
}
else
{
lean_object* v___x_1407_; lean_object* v_toMonadRef_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_8529__overap_1413_; lean_object* v___x_1414_; 
v___x_1407_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1408_ = lean_ctor_get(v___x_1407_, 0);
v___x_1409_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1410_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15);
lean_inc(v_a_1351_);
v___x_1411_ = l_Lean_MessageData_ofExpr(v_a_1351_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
lean_inc_ref(v_toMonadRef_1408_);
lean_inc_ref(v___x_1330_);
v___x_8529__overap_1413_ = l_Lean_addTrace___redArg(v___x_1330_, v___x_1333_, v_toMonadRef_1408_, v___x_1409_, v___x_1352_, v___x_1412_);
lean_inc(v_a_1289_);
lean_inc_ref(v_a_1288_);
lean_inc(v_a_1287_);
lean_inc_ref(v_a_1286_);
v___x_1414_ = lean_apply_5(v___x_8529__overap_1413_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, lean_box(0));
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_dec_ref(v___x_1414_);
v___y_1374_ = v_a_1286_;
v___y_1375_ = v_a_1287_;
v___y_1376_ = v_a_1288_;
v___y_1377_ = v_a_1289_;
goto v___jp_1373_;
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v___f_1360_);
lean_dec(v_a_1351_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_below_1282_);
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
v___jp_1361_:
{
lean_object* v_dummy_1366_; lean_object* v_nargs_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_8194__overap_1371_; lean_object* v___x_1372_; 
v_dummy_1366_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1367_ = l_Lean_Expr_getAppNumArgs(v_a_1351_);
lean_inc(v_nargs_1367_);
v___x_1368_ = lean_mk_array(v_nargs_1367_, v_dummy_1366_);
v___x_1369_ = lean_unsigned_to_nat(1u);
v___x_1370_ = lean_nat_sub(v_nargs_1367_, v___x_1369_);
lean_dec(v_nargs_1367_);
v___x_8194__overap_1371_ = l_Lean_Expr_withAppAux___redArg(v___f_1360_, v_a_1351_, v___x_1368_, v___x_1370_);
lean_inc(v___y_1365_);
lean_inc_ref(v___y_1364_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
v___x_1372_ = lean_apply_5(v___x_8194__overap_1371_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, lean_box(0));
return v___x_1372_;
}
v___jp_1373_:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_Meta_isTypeCorrect(v_below_1282_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; uint8_t v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref(v___x_1378_);
v___x_1380_ = lean_unbox(v_a_1379_);
lean_dec(v_a_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v_a_1382_; uint8_t v___x_1383_; 
v___x_1381_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v___x_1352_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = lean_unbox(v_a_1382_);
lean_dec(v_a_1382_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v___x_1330_);
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
v___y_1365_ = v___y_1377_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1384_; lean_object* v_toMonadRef_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_8507__overap_1388_; lean_object* v___x_1389_; 
v___x_1384_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1385_ = lean_ctor_get(v___x_1384_, 0);
v___x_1386_ = l_Lean_Meta_instAddMessageContextMetaM;
v___x_1387_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_toMonadRef_1385_);
v___x_8507__overap_1388_ = l_Lean_addTrace___redArg(v___x_1330_, v___x_1333_, v_toMonadRef_1385_, v___x_1386_, v___x_1352_, v___x_1387_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc_ref(v___y_1374_);
v___x_1389_ = lean_apply_5(v___x_8507__overap_1388_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, lean_box(0));
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_dec_ref(v___x_1389_);
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
v___y_1365_ = v___y_1377_;
goto v___jp_1361_;
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v___f_1360_);
lean_dec(v_a_1351_);
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_a_1390_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1330_);
v___y_1362_ = v___y_1374_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
v___y_1365_ = v___y_1377_;
goto v___jp_1361_;
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v___f_1360_);
lean_dec(v_a_1351_);
lean_dec_ref(v___x_1330_);
v_a_1398_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1378_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1378_);
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
}
else
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1430_; 
lean_dec_ref(v___x_1349_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_k_1285_);
lean_dec_ref(v_positions_1284_);
lean_dec(v_numIndParams_1283_);
lean_dec_ref(v_below_1282_);
v_a_1423_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1425_ = v___x_1350_;
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1350_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1430_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1428_; 
if (v_isShared_1426_ == 0)
{
v___x_1428_ = v___x_1425_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
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
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
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
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
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
lean_object* v___x_1482_; lean_object* v_traceState_1483_; lean_object* v_traces_1484_; lean_object* v___x_1485_; lean_object* v_traceState_1486_; lean_object* v_env_1487_; lean_object* v_nextMacroScope_1488_; lean_object* v_ngen_1489_; lean_object* v_auxDeclNGen_1490_; lean_object* v_cache_1491_; lean_object* v_messages_1492_; lean_object* v_infoState_1493_; lean_object* v_snapshotTasks_1494_; lean_object* v_newDecls_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1514_; 
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
v_newDecls_1495_ = lean_ctor_get(v___x_1485_, 9);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1497_ = v___x_1485_;
v_isShared_1498_ = v_isSharedCheck_1514_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_newDecls_1495_);
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
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1514_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint64_t v_tid_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1512_; 
v_tid_1499_ = lean_ctor_get_uint64(v_traceState_1486_, sizeof(void*)*1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_traceState_1486_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_traceState_1486_, 0);
lean_dec(v_unused_1513_);
v___x_1501_ = v_traceState_1486_;
v_isShared_1502_ = v_isSharedCheck_1512_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v_traceState_1486_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1512_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1503_);
lean_ctor_set_uint64(v_reuseFailAlloc_1511_, sizeof(void*)*1, v_tid_1499_);
v___x_1505_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v___x_1505_);
v___x_1507_ = v___x_1497_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_env_1487_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_nextMacroScope_1488_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_ngen_1489_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_auxDeclNGen_1490_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1510_, 5, v_cache_1491_);
lean_ctor_set(v_reuseFailAlloc_1510_, 6, v_messages_1492_);
lean_ctor_set(v_reuseFailAlloc_1510_, 7, v_infoState_1493_);
lean_ctor_set(v_reuseFailAlloc_1510_, 8, v_snapshotTasks_1494_);
lean_ctor_set(v_reuseFailAlloc_1510_, 9, v_newDecls_1495_);
v___x_1507_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_st_ref_set(v___y_1480_, v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v_traces_1484_);
return v___x_1509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1515_);
lean_dec(v___y_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1521_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1530_, lean_object* v_opt_1531_){
_start:
{
lean_object* v_name_1532_; lean_object* v_defValue_1533_; lean_object* v_map_1534_; lean_object* v___x_1535_; 
v_name_1532_ = lean_ctor_get(v_opt_1531_, 0);
v_defValue_1533_ = lean_ctor_get(v_opt_1531_, 1);
v_map_1534_ = lean_ctor_get(v_opts_1530_, 0);
v___x_1535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1534_, v_name_1532_);
if (lean_obj_tag(v___x_1535_) == 0)
{
uint8_t v___x_1536_; 
v___x_1536_ = lean_unbox(v_defValue_1533_);
return v___x_1536_;
}
else
{
lean_object* v_val_1537_; 
v_val_1537_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_val_1537_);
lean_dec_ref(v___x_1535_);
if (lean_obj_tag(v_val_1537_) == 1)
{
uint8_t v_v_1538_; 
v_v_1538_ = lean_ctor_get_uint8(v_val_1537_, 0);
lean_dec_ref(v_val_1537_);
return v_v_1538_;
}
else
{
uint8_t v___x_1539_; 
lean_dec(v_val_1537_);
v___x_1539_ = lean_unbox(v_defValue_1533_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1540_, lean_object* v_opt_1541_){
_start:
{
uint8_t v_res_1542_; lean_object* v_r_1543_; 
v_res_1542_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1540_, v_opt_1541_);
lean_dec_ref(v_opt_1541_);
lean_dec_ref(v_opts_1540_);
v_r_1543_ = lean_box(v_res_1542_);
return v_r_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1544_, lean_object* v_fnIndex_1545_, lean_object* v_recArg_1546_, lean_object* v_below_1547_, lean_object* v_Cs_1548_, lean_object* v_belowDict_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_array_get_borrowed(v___x_1544_, v_Cs_1548_, v_fnIndex_1545_);
lean_inc(v___x_1555_);
v___x_1556_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1555_, v_belowDict_1549_, v_recArg_1546_, v_below_1547_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1557_, lean_object* v_fnIndex_1558_, lean_object* v_recArg_1559_, lean_object* v_below_1560_, lean_object* v_Cs_1561_, lean_object* v_belowDict_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1557_, v_fnIndex_1558_, v_recArg_1559_, v_below_1560_, v_Cs_1561_, v_belowDict_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec_ref(v_Cs_1561_);
lean_dec(v_fnIndex_1558_);
lean_dec_ref(v___x_1557_);
return v_res_1568_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1571_ = l_Lean_stringToMessageData(v___x_1570_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1574_ = l_Lean_stringToMessageData(v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1575_, lean_object* v_recArg_1576_, lean_object* v_x_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v___x_1583_; 
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc(v___y_1579_);
lean_inc_ref(v___y_1578_);
v___x_1583_ = lean_infer_type(v_below_1575_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1598_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1598_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1598_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1588_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1589_ = l_Lean_MessageData_ofExpr(v_recArg_1576_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
v___x_1593_ = l_Lean_MessageData_ofExpr(v_a_1584_);
v___x_1594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1592_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1594_);
v___x_1596_ = v___x_1586_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
lean_dec_ref(v_recArg_1576_);
v_a_1599_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v___x_1583_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1583_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1607_, lean_object* v_recArg_1608_, lean_object* v_x_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1607_, v_recArg_1608_, v_x_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec_ref(v_x_1609_);
return v_res_1615_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_e_1616_){
_start:
{
if (lean_obj_tag(v_e_1616_) == 0)
{
uint8_t v___x_1617_; 
v___x_1617_ = 2;
return v___x_1617_;
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = 0;
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_e_1619_){
_start:
{
uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_e_1619_);
lean_dec_ref(v_e_1619_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1622_, lean_object* v_opt_1623_){
_start:
{
lean_object* v_name_1624_; lean_object* v_defValue_1625_; lean_object* v_map_1626_; lean_object* v___x_1627_; 
v_name_1624_ = lean_ctor_get(v_opt_1623_, 0);
v_defValue_1625_ = lean_ctor_get(v_opt_1623_, 1);
v_map_1626_ = lean_ctor_get(v_opts_1622_, 0);
v___x_1627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1626_, v_name_1624_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_inc(v_defValue_1625_);
return v_defValue_1625_;
}
else
{
lean_object* v_val_1628_; 
v_val_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_val_1628_);
lean_dec_ref(v___x_1627_);
if (lean_obj_tag(v_val_1628_) == 3)
{
lean_object* v_v_1629_; 
v_v_1629_ = lean_ctor_get(v_val_1628_, 0);
lean_inc(v_v_1629_);
lean_dec_ref(v_val_1628_);
return v_v_1629_;
}
else
{
lean_dec(v_val_1628_);
lean_inc(v_defValue_1625_);
return v_defValue_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1630_, lean_object* v_opt_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1630_, v_opt_1631_);
lean_dec_ref(v_opt_1631_);
lean_dec_ref(v_opts_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(lean_object* v_x_1633_){
_start:
{
if (lean_obj_tag(v_x_1633_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_a_1635_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v_x_1633_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v_x_1633_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
lean_ctor_set_tag(v___x_1637_, 1);
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v_x_1633_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1633_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v_x_1633_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v_x_1633_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 0);
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg___boxed(lean_object* v_x_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(size_t v_sz_1654_, size_t v_i_1655_, lean_object* v_bs_1656_){
_start:
{
uint8_t v___x_1657_; 
v___x_1657_ = lean_usize_dec_lt(v_i_1655_, v_sz_1654_);
if (v___x_1657_ == 0)
{
return v_bs_1656_;
}
else
{
lean_object* v_v_1658_; lean_object* v_msg_1659_; lean_object* v___x_1660_; lean_object* v_bs_x27_1661_; size_t v___x_1662_; size_t v___x_1663_; lean_object* v___x_1664_; 
v_v_1658_ = lean_array_uget_borrowed(v_bs_1656_, v_i_1655_);
v_msg_1659_ = lean_ctor_get(v_v_1658_, 1);
lean_inc_ref(v_msg_1659_);
v___x_1660_ = lean_unsigned_to_nat(0u);
v_bs_x27_1661_ = lean_array_uset(v_bs_1656_, v_i_1655_, v___x_1660_);
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = lean_usize_add(v_i_1655_, v___x_1662_);
v___x_1664_ = lean_array_uset(v_bs_x27_1661_, v_i_1655_, v_msg_1659_);
v_i_1655_ = v___x_1663_;
v_bs_1656_ = v___x_1664_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_1666_, lean_object* v_i_1667_, lean_object* v_bs_1668_){
_start:
{
size_t v_sz_boxed_1669_; size_t v_i_boxed_1670_; lean_object* v_res_1671_; 
v_sz_boxed_1669_ = lean_unbox_usize(v_sz_1666_);
lean_dec(v_sz_1666_);
v_i_boxed_1670_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_res_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_boxed_1669_, v_i_boxed_1670_, v_bs_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_oldTraces_1672_, lean_object* v_data_1673_, lean_object* v_ref_1674_, lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_fileName_1681_; lean_object* v_fileMap_1682_; lean_object* v_options_1683_; lean_object* v_currRecDepth_1684_; lean_object* v_maxRecDepth_1685_; lean_object* v_ref_1686_; lean_object* v_currNamespace_1687_; lean_object* v_openDecls_1688_; lean_object* v_initHeartbeats_1689_; lean_object* v_maxHeartbeats_1690_; lean_object* v_quotContext_1691_; lean_object* v_currMacroScope_1692_; uint8_t v_diag_1693_; lean_object* v_cancelTk_x3f_1694_; uint8_t v_suppressElabErrors_1695_; lean_object* v_inheritedTraceOptions_1696_; lean_object* v___x_1697_; lean_object* v_traceState_1698_; lean_object* v_traces_1699_; lean_object* v_ref_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; size_t v_sz_1703_; size_t v___x_1704_; lean_object* v___x_1705_; lean_object* v_msg_1706_; lean_object* v___x_1707_; lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1746_; 
v_fileName_1681_ = lean_ctor_get(v___y_1678_, 0);
v_fileMap_1682_ = lean_ctor_get(v___y_1678_, 1);
v_options_1683_ = lean_ctor_get(v___y_1678_, 2);
v_currRecDepth_1684_ = lean_ctor_get(v___y_1678_, 3);
v_maxRecDepth_1685_ = lean_ctor_get(v___y_1678_, 4);
v_ref_1686_ = lean_ctor_get(v___y_1678_, 5);
v_currNamespace_1687_ = lean_ctor_get(v___y_1678_, 6);
v_openDecls_1688_ = lean_ctor_get(v___y_1678_, 7);
v_initHeartbeats_1689_ = lean_ctor_get(v___y_1678_, 8);
v_maxHeartbeats_1690_ = lean_ctor_get(v___y_1678_, 9);
v_quotContext_1691_ = lean_ctor_get(v___y_1678_, 10);
v_currMacroScope_1692_ = lean_ctor_get(v___y_1678_, 11);
v_diag_1693_ = lean_ctor_get_uint8(v___y_1678_, sizeof(void*)*14);
v_cancelTk_x3f_1694_ = lean_ctor_get(v___y_1678_, 12);
v_suppressElabErrors_1695_ = lean_ctor_get_uint8(v___y_1678_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1696_ = lean_ctor_get(v___y_1678_, 13);
v___x_1697_ = lean_st_ref_get(v___y_1679_);
v_traceState_1698_ = lean_ctor_get(v___x_1697_, 4);
lean_inc_ref(v_traceState_1698_);
lean_dec(v___x_1697_);
v_traces_1699_ = lean_ctor_get(v_traceState_1698_, 0);
lean_inc_ref(v_traces_1699_);
lean_dec_ref(v_traceState_1698_);
v_ref_1700_ = l_Lean_replaceRef(v_ref_1674_, v_ref_1686_);
lean_inc_ref(v_inheritedTraceOptions_1696_);
lean_inc(v_cancelTk_x3f_1694_);
lean_inc(v_currMacroScope_1692_);
lean_inc(v_quotContext_1691_);
lean_inc(v_maxHeartbeats_1690_);
lean_inc(v_initHeartbeats_1689_);
lean_inc(v_openDecls_1688_);
lean_inc(v_currNamespace_1687_);
lean_inc(v_maxRecDepth_1685_);
lean_inc(v_currRecDepth_1684_);
lean_inc_ref(v_options_1683_);
lean_inc_ref(v_fileMap_1682_);
lean_inc_ref(v_fileName_1681_);
v___x_1701_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1701_, 0, v_fileName_1681_);
lean_ctor_set(v___x_1701_, 1, v_fileMap_1682_);
lean_ctor_set(v___x_1701_, 2, v_options_1683_);
lean_ctor_set(v___x_1701_, 3, v_currRecDepth_1684_);
lean_ctor_set(v___x_1701_, 4, v_maxRecDepth_1685_);
lean_ctor_set(v___x_1701_, 5, v_ref_1700_);
lean_ctor_set(v___x_1701_, 6, v_currNamespace_1687_);
lean_ctor_set(v___x_1701_, 7, v_openDecls_1688_);
lean_ctor_set(v___x_1701_, 8, v_initHeartbeats_1689_);
lean_ctor_set(v___x_1701_, 9, v_maxHeartbeats_1690_);
lean_ctor_set(v___x_1701_, 10, v_quotContext_1691_);
lean_ctor_set(v___x_1701_, 11, v_currMacroScope_1692_);
lean_ctor_set(v___x_1701_, 12, v_cancelTk_x3f_1694_);
lean_ctor_set(v___x_1701_, 13, v_inheritedTraceOptions_1696_);
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*14, v_diag_1693_);
lean_ctor_set_uint8(v___x_1701_, sizeof(void*)*14 + 1, v_suppressElabErrors_1695_);
v___x_1702_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1699_);
lean_dec_ref(v_traces_1699_);
v_sz_1703_ = lean_array_size(v___x_1702_);
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_spec__4(v_sz_1703_, v___x_1704_, v___x_1702_);
v_msg_1706_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1706_, 0, v_data_1673_);
lean_ctor_set(v_msg_1706_, 1, v_msg_1675_);
lean_ctor_set(v_msg_1706_, 2, v___x_1705_);
v___x_1707_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1706_, v___y_1676_, v___y_1677_, v___x_1701_, v___y_1679_);
lean_dec_ref(v___x_1701_);
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1746_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1746_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v_traceState_1713_; lean_object* v_env_1714_; lean_object* v_nextMacroScope_1715_; lean_object* v_ngen_1716_; lean_object* v_auxDeclNGen_1717_; lean_object* v_cache_1718_; lean_object* v_messages_1719_; lean_object* v_infoState_1720_; lean_object* v_snapshotTasks_1721_; lean_object* v_newDecls_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1745_; 
v___x_1712_ = lean_st_ref_take(v___y_1679_);
v_traceState_1713_ = lean_ctor_get(v___x_1712_, 4);
v_env_1714_ = lean_ctor_get(v___x_1712_, 0);
v_nextMacroScope_1715_ = lean_ctor_get(v___x_1712_, 1);
v_ngen_1716_ = lean_ctor_get(v___x_1712_, 2);
v_auxDeclNGen_1717_ = lean_ctor_get(v___x_1712_, 3);
v_cache_1718_ = lean_ctor_get(v___x_1712_, 5);
v_messages_1719_ = lean_ctor_get(v___x_1712_, 6);
v_infoState_1720_ = lean_ctor_get(v___x_1712_, 7);
v_snapshotTasks_1721_ = lean_ctor_get(v___x_1712_, 8);
v_newDecls_1722_ = lean_ctor_get(v___x_1712_, 9);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1724_ = v___x_1712_;
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_newDecls_1722_);
lean_inc(v_snapshotTasks_1721_);
lean_inc(v_infoState_1720_);
lean_inc(v_messages_1719_);
lean_inc(v_cache_1718_);
lean_inc(v_traceState_1713_);
lean_inc(v_auxDeclNGen_1717_);
lean_inc(v_ngen_1716_);
lean_inc(v_nextMacroScope_1715_);
lean_inc(v_env_1714_);
lean_dec(v___x_1712_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1745_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
uint64_t v_tid_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1743_; 
v_tid_1726_ = lean_ctor_get_uint64(v_traceState_1713_, sizeof(void*)*1);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_traceState_1713_);
if (v_isSharedCheck_1743_ == 0)
{
lean_object* v_unused_1744_; 
v_unused_1744_ = lean_ctor_get(v_traceState_1713_, 0);
lean_dec(v_unused_1744_);
v___x_1728_ = v_traceState_1713_;
v_isShared_1729_ = v_isSharedCheck_1743_;
goto v_resetjp_1727_;
}
else
{
lean_dec(v_traceState_1713_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1743_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_ref_1674_);
lean_ctor_set(v___x_1730_, 1, v_a_1708_);
v___x_1731_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1672_, v___x_1730_);
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
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_env_1714_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_nextMacroScope_1715_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_ngen_1716_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_auxDeclNGen_1717_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 5, v_cache_1718_);
lean_ctor_set(v_reuseFailAlloc_1741_, 6, v_messages_1719_);
lean_ctor_set(v_reuseFailAlloc_1741_, 7, v_infoState_1720_);
lean_ctor_set(v_reuseFailAlloc_1741_, 8, v_snapshotTasks_1721_);
lean_ctor_set(v_reuseFailAlloc_1741_, 9, v_newDecls_1722_);
v___x_1735_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = lean_st_ref_set(v___y_1679_, v___x_1735_);
v___x_1737_ = lean_box(0);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1737_);
v___x_1739_ = v___x_1710_;
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
lean_object* v_fst_1778_; lean_object* v_snd_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1878_; 
v_fst_1778_ = lean_ctor_get(v_resStartStop_1772_, 0);
v_snd_1779_ = lean_ctor_get(v_resStartStop_1772_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_resStartStop_1772_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1781_ = v_resStartStop_1772_;
v_isShared_1782_ = v_isSharedCheck_1878_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_snd_1779_);
lean_inc(v_fst_1778_);
lean_dec(v_resStartStop_1772_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1878_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v_data_1786_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1877_; 
v_fst_1797_ = lean_ctor_get(v_snd_1779_, 0);
v_snd_1798_ = lean_ctor_get(v_snd_1779_, 1);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_snd_1779_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1800_ = v_snd_1779_;
v_isShared_1801_ = v_isSharedCheck_1877_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snd_1798_);
lean_inc(v_fst_1797_);
lean_dec(v_snd_1779_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1877_;
goto v_resetjp_1799_;
}
v___jp_1783_:
{
lean_object* v___x_1787_; 
lean_inc(v___y_1784_);
v___x_1787_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_oldTraces_1770_, v_data_1786_, v___y_1784_, v___y_1785_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; 
lean_dec_ref(v___x_1787_);
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
lean_object* v___x_1802_; uint8_t v___x_1803_; lean_object* v___y_1805_; lean_object* v_a_1806_; uint8_t v___y_1830_; double v___y_1862_; 
v___x_1802_ = l_Lean_trace_profiler;
v___x_1803_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1768_, v___x_1802_);
if (v___x_1803_ == 0)
{
v___y_1830_ = v___x_1803_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1868_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1768_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; double v___x_1871_; double v___x_1872_; double v___x_1873_; 
v___x_1869_ = l_Lean_trace_profiler_threshold;
v___x_1870_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1768_, v___x_1869_);
v___x_1871_ = lean_float_of_nat(v___x_1870_);
v___x_1872_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__4);
v___x_1873_ = lean_float_div(v___x_1871_, v___x_1872_);
v___y_1862_ = v___x_1873_;
goto v___jp_1861_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; double v___x_1876_; 
v___x_1874_ = l_Lean_trace_profiler_threshold;
v___x_1875_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1768_, v___x_1874_);
v___x_1876_ = lean_float_of_nat(v___x_1875_);
v___y_1862_ = v___x_1876_;
goto v___jp_1861_;
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
lean_dec_ref(v___x_1816_);
lean_dec(v_snd_1798_);
lean_dec(v_fst_1797_);
lean_dec_ref(v_tag_1767_);
lean_dec(v_cls_1765_);
v___y_1784_ = v___y_1805_;
v___y_1785_ = v_m_1814_;
v_data_1786_ = v_data_1818_;
goto v___jp_1783_;
}
else
{
lean_object* v_data_1819_; double v___x_1820_; double v___x_1821_; 
lean_dec_ref(v_data_1818_);
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
v___y_1784_ = v___y_1805_;
v___y_1785_ = v_m_1814_;
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
lean_dec_ref(v___x_1826_);
v___y_1805_ = v_ref_1825_;
v_a_1806_ = v_a_1827_;
goto v___jp_1804_;
}
else
{
lean_object* v___x_1828_; 
lean_dec_ref(v___x_1826_);
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
lean_object* v___x_1831_; lean_object* v_traceState_1832_; lean_object* v_env_1833_; lean_object* v_nextMacroScope_1834_; lean_object* v_ngen_1835_; lean_object* v_auxDeclNGen_1836_; lean_object* v_cache_1837_; lean_object* v_messages_1838_; lean_object* v_infoState_1839_; lean_object* v_snapshotTasks_1840_; lean_object* v_newDecls_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1860_; 
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
v_newDecls_1841_ = lean_ctor_get(v___x_1831_, 9);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1843_ = v___x_1831_;
v_isShared_1844_ = v_isSharedCheck_1860_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_newDecls_1841_);
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
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1860_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
uint64_t v_tid_1845_; lean_object* v_traces_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1859_; 
v_tid_1845_ = lean_ctor_get_uint64(v_traceState_1832_, sizeof(void*)*1);
v_traces_1846_ = lean_ctor_get(v_traceState_1832_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_traceState_1832_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1848_ = v_traceState_1832_;
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_traces_1846_);
lean_dec(v_traceState_1832_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1859_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1770_, v_traces_1846_);
lean_dec_ref(v_traces_1846_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1850_);
lean_ctor_set_uint64(v_reuseFailAlloc_1858_, sizeof(void*)*1, v_tid_1845_);
v___x_1852_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 4, v___x_1852_);
v___x_1854_ = v___x_1843_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_env_1833_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_nextMacroScope_1834_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_ngen_1835_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_auxDeclNGen_1836_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1857_, 5, v_cache_1837_);
lean_ctor_set(v_reuseFailAlloc_1857_, 6, v_messages_1838_);
lean_ctor_set(v_reuseFailAlloc_1857_, 7, v_infoState_1839_);
lean_ctor_set(v_reuseFailAlloc_1857_, 8, v_snapshotTasks_1840_);
lean_ctor_set(v_reuseFailAlloc_1857_, 9, v_newDecls_1841_);
v___x_1854_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_st_ref_set(v___y_1776_, v___x_1854_);
v___x_1856_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_fst_1778_);
return v___x_1856_;
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
v___jp_1861_:
{
double v___x_1863_; double v___x_1864_; double v___x_1865_; uint8_t v___x_1866_; 
v___x_1863_ = lean_unbox_float(v_snd_1798_);
v___x_1864_ = lean_unbox_float(v_fst_1797_);
v___x_1865_ = lean_float_sub(v___x_1863_, v___x_1864_);
v___x_1866_ = lean_float_decLt(v___y_1862_, v___x_1865_);
v___y_1830_ = v___x_1866_;
goto v___jp_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1879_, lean_object* v_collapsed_1880_, lean_object* v_tag_1881_, lean_object* v_opts_1882_, lean_object* v_clsEnabled_1883_, lean_object* v_oldTraces_1884_, lean_object* v_msg_1885_, lean_object* v_resStartStop_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
uint8_t v_collapsed_boxed_1892_; uint8_t v_clsEnabled_boxed_1893_; lean_object* v_res_1894_; 
v_collapsed_boxed_1892_ = lean_unbox(v_collapsed_1880_);
v_clsEnabled_boxed_1893_ = lean_unbox(v_clsEnabled_1883_);
v_res_1894_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1879_, v_collapsed_boxed_1892_, v_tag_1881_, v_opts_1882_, v_clsEnabled_boxed_1893_, v_oldTraces_1884_, v_msg_1885_, v_resStartStop_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v_opts_1882_);
return v_res_1894_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1896_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1897_ = l_Lean_Name_append(v___x_1896_, v___x_1895_);
return v___x_1897_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__1(void){
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
lean_object* v_options_1910_; lean_object* v_inheritedTraceOptions_1911_; uint8_t v_hasTrace_1912_; lean_object* v___x_1913_; lean_object* v___f_1914_; 
v_options_1910_ = lean_ctor_get(v_a_1907_, 2);
v_inheritedTraceOptions_1911_ = lean_ctor_get(v_a_1907_, 13);
v_hasTrace_1912_ = lean_ctor_get_uint8(v_options_1910_, sizeof(void*)*1);
v___x_1913_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1900_);
lean_inc_ref(v_recArg_1904_);
v___f_1914_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1914_, 0, v___x_1913_);
lean_closure_set(v___f_1914_, 1, v_fnIndex_1903_);
lean_closure_set(v___f_1914_, 2, v_recArg_1904_);
lean_closure_set(v___f_1914_, 3, v_below_1900_);
if (v_hasTrace_1912_ == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref(v_recArg_1904_);
v___x_1915_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1914_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1915_;
}
else
{
lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v_a_1924_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v_a_1939_; 
lean_inc_ref(v_below_1900_);
v___f_1916_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1916_, 0, v_below_1900_);
lean_closure_set(v___f_1916_, 1, v_recArg_1904_);
v___x_1917_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1918_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1919_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1911_, v_options_1910_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1989_ = l_Lean_trace_profiler;
v___x_1990_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1910_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_dec_ref(v___f_1916_);
v___x_1991_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1914_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1991_;
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
v___jp_1921_:
{
lean_object* v___x_1925_; double v___x_1926_; double v___x_1927_; double v___x_1928_; double v___x_1929_; double v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1925_ = lean_io_mono_nanos_now();
v___x_1926_ = lean_float_of_nat(v___y_1923_);
v___x_1927_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__1, &l_Lean_Elab_Structural_toBelow___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___closed__1);
v___x_1928_ = lean_float_div(v___x_1926_, v___x_1927_);
v___x_1929_ = lean_float_of_nat(v___x_1925_);
v___x_1930_ = lean_float_div(v___x_1929_, v___x_1927_);
v___x_1931_ = lean_box_float(v___x_1928_);
v___x_1932_ = lean_box_float(v___x_1930_);
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1924_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1917_, v_hasTrace_1912_, v___x_1918_, v_options_1910_, v___x_1920_, v___y_1922_, v___f_1916_, v___x_1934_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1935_;
}
v___jp_1936_:
{
lean_object* v___x_1940_; double v___x_1941_; double v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
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
v___x_1947_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1917_, v_hasTrace_1912_, v___x_1918_, v_options_1910_, v___x_1920_, v___y_1938_, v___f_1916_, v___x_1946_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
return v___x_1947_;
}
v___jp_1948_:
{
lean_object* v___x_1949_; lean_object* v_a_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1949_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1908_);
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1952_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1910_, v___x_1951_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = lean_io_mono_nanos_now();
v___x_1954_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1914_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
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
v___y_1922_ = v_a_1950_;
v___y_1923_ = v___x_1953_;
v_a_1924_ = v___x_1960_;
goto v___jp_1921_;
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
v___y_1922_ = v_a_1950_;
v___y_1923_ = v___x_1953_;
v_a_1924_ = v___x_1968_;
goto v___jp_1921_;
}
}
}
}
else
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = lean_io_get_num_heartbeats();
v___x_1972_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1900_, v_numIndParams_1901_, v_positions_1902_, v___f_1914_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
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
v___y_1937_ = v___x_1971_;
v___y_1938_ = v_a_1950_;
v_a_1939_ = v___x_1978_;
goto v___jp_1936_;
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
v___y_1937_ = v___x_1971_;
v___y_1938_ = v_a_1950_;
v_a_1939_ = v___x_1986_;
goto v___jp_1936_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1992_, lean_object* v_numIndParams_1993_, lean_object* v_positions_1994_, lean_object* v_fnIndex_1995_, lean_object* v_recArg_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_Elab_Structural_toBelow(v_below_1992_, v_numIndParams_1993_, v_positions_1994_, v_fnIndex_1995_, v_recArg_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_00_u03b1_2003_, lean_object* v_x_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___redArg(v_x_2004_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2011_, lean_object* v_x_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_00_u03b1_2011_, v_x_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_2019_, lean_object* v___y_2020_, lean_object* v_b_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2027_; 
lean_inc(v___y_2025_);
lean_inc_ref(v___y_2024_);
lean_inc(v___y_2023_);
lean_inc_ref(v___y_2022_);
lean_inc(v___y_2020_);
v___x_2027_ = lean_apply_7(v_k_2019_, v_b_2021_, v___y_2020_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, lean_box(0));
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_2028_, lean_object* v___y_2029_, lean_object* v_b_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_2028_, v___y_2029_, v_b_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2029_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_2037_, uint8_t v_bi_2038_, lean_object* v_type_2039_, lean_object* v_k_2040_, uint8_t v_kind_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___f_2048_; lean_object* v___x_2049_; 
lean_inc(v___y_2042_);
v___f_2048_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2048_, 0, v_k_2040_);
lean_closure_set(v___f_2048_, 1, v___y_2042_);
v___x_2049_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2037_, v_bi_2038_, v_type_2039_, v___f_2048_, v_kind_2041_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2049_) == 0)
{
return v___x_2049_;
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2049_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2058_, lean_object* v_bi_2059_, lean_object* v_type_2060_, lean_object* v_k_2061_, lean_object* v_kind_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v_bi_boxed_2069_; uint8_t v_kind_boxed_2070_; lean_object* v_res_2071_; 
v_bi_boxed_2069_ = lean_unbox(v_bi_2059_);
v_kind_boxed_2070_ = lean_unbox(v_kind_2062_);
v_res_2071_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2058_, v_bi_boxed_2069_, v_type_2060_, v_k_2061_, v_kind_boxed_2070_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2072_, lean_object* v_name_2073_, uint8_t v_bi_2074_, lean_object* v_type_2075_, lean_object* v_k_2076_, uint8_t v_kind_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2073_, v_bi_2074_, v_type_2075_, v_k_2076_, v_kind_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_name_2086_, lean_object* v_bi_2087_, lean_object* v_type_2088_, lean_object* v_k_2089_, lean_object* v_kind_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
uint8_t v_bi_boxed_2097_; uint8_t v_kind_boxed_2098_; lean_object* v_res_2099_; 
v_bi_boxed_2097_ = lean_unbox(v_bi_2087_);
v_kind_boxed_2098_ = lean_unbox(v_kind_2090_);
v_res_2099_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2085_, v_name_2086_, v_bi_boxed_2097_, v_type_2088_, v_k_2089_, v_kind_boxed_2098_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2100_, lean_object* v___y_2101_, lean_object* v_b_2102_, lean_object* v_c_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; 
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___y_2105_);
lean_inc_ref(v___y_2104_);
lean_inc(v___y_2101_);
v___x_2109_ = lean_apply_8(v_k_2100_, v_b_2102_, v_c_2103_, v___y_2101_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, lean_box(0));
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2110_, lean_object* v___y_2111_, lean_object* v_b_2112_, lean_object* v_c_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2110_, v___y_2111_, v_b_2112_, v_c_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2111_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2120_, lean_object* v_maxFVars_2121_, lean_object* v_k_2122_, uint8_t v_cleanupAnnotations_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___f_2130_; uint8_t v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
lean_inc(v___y_2124_);
v___f_2130_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2130_, 0, v_k_2122_);
lean_closure_set(v___f_2130_, 1, v___y_2124_);
v___x_2131_ = 1;
v___x_2132_ = 0;
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_maxFVars_2121_);
v___x_2134_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2120_, v___x_2131_, v___x_2132_, v___x_2131_, v___x_2132_, v___x_2133_, v___f_2130_, v_cleanupAnnotations_2123_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec_ref(v___x_2133_);
if (lean_obj_tag(v___x_2134_) == 0)
{
return v___x_2134_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2134_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2134_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2143_, lean_object* v_maxFVars_2144_, lean_object* v_k_2145_, lean_object* v_cleanupAnnotations_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2153_; lean_object* v_res_2154_; 
v_cleanupAnnotations_boxed_2153_ = lean_unbox(v_cleanupAnnotations_2146_);
v_res_2154_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2143_, v_maxFVars_2144_, v_k_2145_, v_cleanupAnnotations_boxed_2153_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2155_, lean_object* v_e_2156_, lean_object* v_maxFVars_2157_, lean_object* v_k_2158_, uint8_t v_cleanupAnnotations_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2156_, v_maxFVars_2157_, v_k_2158_, v_cleanupAnnotations_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_e_2168_, lean_object* v_maxFVars_2169_, lean_object* v_k_2170_, lean_object* v_cleanupAnnotations_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2178_; lean_object* v_res_2179_; 
v_cleanupAnnotations_boxed_2178_ = lean_unbox(v_cleanupAnnotations_2171_);
v_res_2179_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2167_, v_e_2168_, v_maxFVars_2169_, v_k_2170_, v_cleanupAnnotations_boxed_2178_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2180_, lean_object* v_msg_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_ref_2187_; lean_object* v___x_2188_; lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2234_; 
v_ref_2187_ = lean_ctor_get(v___y_2184_, 5);
v___x_2188_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2234_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2234_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v_traceState_2194_; lean_object* v_env_2195_; lean_object* v_nextMacroScope_2196_; lean_object* v_ngen_2197_; lean_object* v_auxDeclNGen_2198_; lean_object* v_cache_2199_; lean_object* v_messages_2200_; lean_object* v_infoState_2201_; lean_object* v_snapshotTasks_2202_; lean_object* v_newDecls_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2233_; 
v___x_2193_ = lean_st_ref_take(v___y_2185_);
v_traceState_2194_ = lean_ctor_get(v___x_2193_, 4);
v_env_2195_ = lean_ctor_get(v___x_2193_, 0);
v_nextMacroScope_2196_ = lean_ctor_get(v___x_2193_, 1);
v_ngen_2197_ = lean_ctor_get(v___x_2193_, 2);
v_auxDeclNGen_2198_ = lean_ctor_get(v___x_2193_, 3);
v_cache_2199_ = lean_ctor_get(v___x_2193_, 5);
v_messages_2200_ = lean_ctor_get(v___x_2193_, 6);
v_infoState_2201_ = lean_ctor_get(v___x_2193_, 7);
v_snapshotTasks_2202_ = lean_ctor_get(v___x_2193_, 8);
v_newDecls_2203_ = lean_ctor_get(v___x_2193_, 9);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2205_ = v___x_2193_;
v_isShared_2206_ = v_isSharedCheck_2233_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_newDecls_2203_);
lean_inc(v_snapshotTasks_2202_);
lean_inc(v_infoState_2201_);
lean_inc(v_messages_2200_);
lean_inc(v_cache_2199_);
lean_inc(v_traceState_2194_);
lean_inc(v_auxDeclNGen_2198_);
lean_inc(v_ngen_2197_);
lean_inc(v_nextMacroScope_2196_);
lean_inc(v_env_2195_);
lean_dec(v___x_2193_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2233_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
uint64_t v_tid_2207_; lean_object* v_traces_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2232_; 
v_tid_2207_ = lean_ctor_get_uint64(v_traceState_2194_, sizeof(void*)*1);
v_traces_2208_ = lean_ctor_get(v_traceState_2194_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_traceState_2194_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2210_ = v_traceState_2194_;
v_isShared_2211_ = v_isSharedCheck_2232_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_traces_2208_);
lean_dec(v_traceState_2194_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2232_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; double v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2214_ = 0;
v___x_2215_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2216_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2216_, 0, v_cls_2180_);
lean_ctor_set(v___x_2216_, 1, v___x_2212_);
lean_ctor_set(v___x_2216_, 2, v___x_2215_);
lean_ctor_set_float(v___x_2216_, sizeof(void*)*3, v___x_2213_);
lean_ctor_set_float(v___x_2216_, sizeof(void*)*3 + 8, v___x_2213_);
lean_ctor_set_uint8(v___x_2216_, sizeof(void*)*3 + 16, v___x_2214_);
v___x_2217_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2218_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v_a_2189_);
lean_ctor_set(v___x_2218_, 2, v___x_2217_);
lean_inc(v_ref_2187_);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v_ref_2187_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = l_Lean_PersistentArray_push___redArg(v_traces_2208_, v___x_2219_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2220_);
v___x_2222_ = v___x_2210_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2220_);
lean_ctor_set_uint64(v_reuseFailAlloc_2231_, sizeof(void*)*1, v_tid_2207_);
v___x_2222_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 4, v___x_2222_);
v___x_2224_ = v___x_2205_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_env_2195_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v_nextMacroScope_2196_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_ngen_2197_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_auxDeclNGen_2198_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v___x_2222_);
lean_ctor_set(v_reuseFailAlloc_2230_, 5, v_cache_2199_);
lean_ctor_set(v_reuseFailAlloc_2230_, 6, v_messages_2200_);
lean_ctor_set(v_reuseFailAlloc_2230_, 7, v_infoState_2201_);
lean_ctor_set(v_reuseFailAlloc_2230_, 8, v_snapshotTasks_2202_);
lean_ctor_set(v_reuseFailAlloc_2230_, 9, v_newDecls_2203_);
v___x_2224_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2225_ = lean_st_ref_set(v___y_2185_, v___x_2224_);
v___x_2226_ = lean_box(0);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2226_);
v___x_2228_ = v___x_2191_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2235_, lean_object* v_msg_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2235_, v_msg_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2243_, lean_object* v_as_2244_, size_t v_i_2245_, size_t v_stop_2246_){
_start:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_usize_dec_eq(v_i_2245_, v_stop_2246_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2248_; lean_object* v_fnName_2249_; lean_object* v_recArgPos_2250_; uint8_t v___x_2251_; 
v___x_2248_ = lean_array_uget_borrowed(v_as_2244_, v_i_2245_);
v_fnName_2249_ = lean_ctor_get(v___x_2248_, 0);
v_recArgPos_2250_ = lean_ctor_get(v___x_2248_, 2);
lean_inc(v_recArgPos_2250_);
lean_inc(v_fnName_2249_);
v___x_2251_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2249_, v_recArgPos_2250_, v_e_2243_);
if (v___x_2251_ == 0)
{
size_t v___x_2252_; size_t v___x_2253_; 
v___x_2252_ = ((size_t)1ULL);
v___x_2253_ = lean_usize_add(v_i_2245_, v___x_2252_);
v_i_2245_ = v___x_2253_;
goto _start;
}
else
{
return v___x_2251_;
}
}
else
{
uint8_t v___x_2255_; 
v___x_2255_ = 0;
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2256_, lean_object* v_as_2257_, lean_object* v_i_2258_, lean_object* v_stop_2259_){
_start:
{
size_t v_i_boxed_2260_; size_t v_stop_boxed_2261_; uint8_t v_res_2262_; lean_object* v_r_2263_; 
v_i_boxed_2260_ = lean_unbox_usize(v_i_2258_);
lean_dec(v_i_2258_);
v_stop_boxed_2261_ = lean_unbox_usize(v_stop_2259_);
lean_dec(v_stop_2259_);
v_res_2262_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2256_, v_as_2257_, v_i_boxed_2260_, v_stop_boxed_2261_);
lean_dec_ref(v_as_2257_);
lean_dec_ref(v_e_2256_);
v_r_2263_ = lean_box(v_res_2262_);
return v_r_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2264_, lean_object* v_____do__lift_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_options_2272_; uint8_t v_hasTrace_2273_; 
v_options_2272_ = lean_ctor_get(v___y_2269_, 2);
v_hasTrace_2273_ = lean_ctor_get_uint8(v_options_2272_, sizeof(void*)*1);
if (v_hasTrace_2273_ == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
lean_dec(v___x_2264_);
v___x_2274_ = lean_box(v_hasTrace_2273_);
v___x_2275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2276_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2277_ = l_Lean_Name_append(v___x_2276_, v___x_2264_);
v___x_2278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2265_, v_options_2272_, v___x_2277_);
lean_dec(v___x_2277_);
v___x_2279_ = lean_box(v___x_2278_);
v___x_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
return v___x_2280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2281_, lean_object* v_____do__lift_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2281_, v_____do__lift_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v_____do__lift_2282_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v_env_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = lean_st_ref_get(v___y_2291_);
v_env_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc_ref(v_env_2294_);
lean_dec(v___x_2293_);
v___x_2295_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2294_, v_declName_2290_);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2297_, v___y_2298_);
lean_dec(v___y_2298_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v_toApplicative_2309_; lean_object* v_toFunctor_2310_; lean_object* v_toSeq_2311_; lean_object* v_toSeqLeft_2312_; lean_object* v_toSeqRight_2313_; lean_object* v___f_2314_; lean_object* v___f_2315_; lean_object* v___f_2316_; lean_object* v___f_2317_; lean_object* v___x_2318_; lean_object* v___f_2319_; lean_object* v___f_2320_; lean_object* v___f_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v_toApplicative_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2357_; 
v___x_2308_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2309_ = lean_ctor_get(v___x_2308_, 0);
v_toFunctor_2310_ = lean_ctor_get(v_toApplicative_2309_, 0);
v_toSeq_2311_ = lean_ctor_get(v_toApplicative_2309_, 2);
v_toSeqLeft_2312_ = lean_ctor_get(v_toApplicative_2309_, 3);
v_toSeqRight_2313_ = lean_ctor_get(v_toApplicative_2309_, 4);
v___f_2314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2315_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2310_, 2);
v___f_2316_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2316_, 0, v_toFunctor_2310_);
v___f_2317_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2317_, 0, v_toFunctor_2310_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___f_2316_);
lean_ctor_set(v___x_2318_, 1, v___f_2317_);
lean_inc(v_toSeqRight_2313_);
v___f_2319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2319_, 0, v_toSeqRight_2313_);
lean_inc(v_toSeqLeft_2312_);
v___f_2320_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2320_, 0, v_toSeqLeft_2312_);
lean_inc(v_toSeq_2311_);
v___f_2321_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2321_, 0, v_toSeq_2311_);
v___x_2322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2318_);
lean_ctor_set(v___x_2322_, 1, v___f_2314_);
lean_ctor_set(v___x_2322_, 2, v___f_2321_);
lean_ctor_set(v___x_2322_, 3, v___f_2320_);
lean_ctor_set(v___x_2322_, 4, v___f_2319_);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
lean_ctor_set(v___x_2323_, 1, v___f_2315_);
v___x_2324_ = l_StateRefT_x27_instMonad___redArg(v___x_2323_);
v_toApplicative_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2357_ == 0)
{
lean_object* v_unused_2358_; 
v_unused_2358_ = lean_ctor_get(v___x_2324_, 1);
lean_dec(v_unused_2358_);
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2357_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_toApplicative_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2357_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_toFunctor_2329_; lean_object* v_toSeq_2330_; lean_object* v_toSeqLeft_2331_; lean_object* v_toSeqRight_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2355_; 
v_toFunctor_2329_ = lean_ctor_get(v_toApplicative_2325_, 0);
v_toSeq_2330_ = lean_ctor_get(v_toApplicative_2325_, 2);
v_toSeqLeft_2331_ = lean_ctor_get(v_toApplicative_2325_, 3);
v_toSeqRight_2332_ = lean_ctor_get(v_toApplicative_2325_, 4);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_toApplicative_2325_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v_toApplicative_2325_, 1);
lean_dec(v_unused_2356_);
v___x_2334_ = v_toApplicative_2325_;
v_isShared_2335_ = v_isSharedCheck_2355_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_toSeqRight_2332_);
lean_inc(v_toSeqLeft_2331_);
lean_inc(v_toSeq_2330_);
lean_inc(v_toFunctor_2329_);
lean_dec(v_toApplicative_2325_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2355_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___f_2336_; lean_object* v___f_2337_; lean_object* v___f_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___f_2343_; lean_object* v___x_2345_; 
v___f_2336_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2337_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2329_);
v___f_2338_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2338_, 0, v_toFunctor_2329_);
v___f_2339_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2339_, 0, v_toFunctor_2329_);
v___x_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___f_2338_);
lean_ctor_set(v___x_2340_, 1, v___f_2339_);
v___f_2341_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2341_, 0, v_toSeqRight_2332_);
v___f_2342_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2342_, 0, v_toSeqLeft_2331_);
v___f_2343_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2343_, 0, v_toSeq_2330_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 4, v___f_2341_);
lean_ctor_set(v___x_2334_, 3, v___f_2342_);
lean_ctor_set(v___x_2334_, 2, v___f_2343_);
lean_ctor_set(v___x_2334_, 1, v___f_2336_);
lean_ctor_set(v___x_2334_, 0, v___x_2340_);
v___x_2345_ = v___x_2334_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___f_2336_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v___f_2343_);
lean_ctor_set(v_reuseFailAlloc_2354_, 3, v___f_2342_);
lean_ctor_set(v_reuseFailAlloc_2354_, 4, v___f_2341_);
v___x_2345_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v___f_2337_);
lean_ctor_set(v___x_2327_, 0, v___x_2345_);
v___x_2347_ = v___x_2327_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v___f_2337_);
v___x_2347_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_27629__overap_2351_; lean_object* v___x_2352_; 
v___x_2348_ = l_StateRefT_x27_instMonad___redArg(v___x_2347_);
v___x_2349_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2350_ = l_instInhabitedOfMonad___redArg(v___x_2348_, v___x_2349_);
v___x_27629__overap_2351_ = lean_panic_fn_borrowed(v___x_2350_, v_msg_2301_);
lean_dec(v___x_2350_);
lean_inc(v___y_2306_);
lean_inc_ref(v___y_2305_);
lean_inc(v___y_2304_);
lean_inc_ref(v___y_2303_);
lean_inc(v___y_2302_);
v___x_2352_ = lean_apply_6(v___x_27629__overap_2351_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, lean_box(0));
return v___x_2352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
return v_res_2366_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2367_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2371_ = lean_unsigned_to_nat(0u);
v___x_2372_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
lean_ctor_set(v___x_2372_, 2, v___x_2371_);
lean_ctor_set(v___x_2372_, 3, v___x_2371_);
lean_ctor_set(v___x_2372_, 4, v___x_2370_);
lean_ctor_set(v___x_2372_, 5, v___x_2370_);
lean_ctor_set(v___x_2372_, 6, v___x_2370_);
lean_ctor_set(v___x_2372_, 7, v___x_2370_);
lean_ctor_set(v___x_2372_, 8, v___x_2370_);
lean_ctor_set(v___x_2372_, 9, v___x_2370_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_unsigned_to_nat(32u);
v___x_2374_ = lean_mk_empty_array_with_capacity(v___x_2373_);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2376_ = ((size_t)5ULL);
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = lean_unsigned_to_nat(32u);
v___x_2379_ = lean_mk_empty_array_with_capacity(v___x_2378_);
v___x_2380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2381_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v___x_2379_);
lean_ctor_set(v___x_2381_, 2, v___x_2377_);
lean_ctor_set(v___x_2381_, 3, v___x_2377_);
lean_ctor_set_usize(v___x_2381_, 4, v___x_2376_);
return v___x_2381_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2382_ = lean_box(1);
v___x_2383_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2384_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2385_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
lean_ctor_set(v___x_2385_, 1, v___x_2383_);
lean_ctor_set(v___x_2385_, 2, v___x_2382_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2399_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2400_ = l_Lean_stringToMessageData(v___x_2399_);
return v___x_2400_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2403_ = l_Lean_stringToMessageData(v___x_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2406_ = l_Lean_stringToMessageData(v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2407_, lean_object* v_declHint_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v_env_2412_; uint8_t v___x_2413_; 
v___x_2411_ = lean_st_ref_get(v___y_2409_);
v_env_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc_ref(v_env_2412_);
lean_dec(v___x_2411_);
v___x_2413_ = l_Lean_Name_isAnonymous(v_declHint_2408_);
if (v___x_2413_ == 0)
{
uint8_t v_isExporting_2414_; 
v_isExporting_2414_ = lean_ctor_get_uint8(v_env_2412_, sizeof(void*)*8);
if (v_isExporting_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_dec_ref(v_env_2412_);
lean_dec(v_declHint_2408_);
v___x_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2415_, 0, v_msg_2407_);
return v___x_2415_;
}
else
{
lean_object* v___x_2416_; uint8_t v___x_2417_; 
lean_inc_ref(v_env_2412_);
v___x_2416_ = l_Lean_Environment_setExporting(v_env_2412_, v___x_2413_);
lean_inc(v_declHint_2408_);
lean_inc_ref(v___x_2416_);
v___x_2417_ = l_Lean_Environment_contains(v___x_2416_, v_declHint_2408_, v_isExporting_2414_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
lean_dec_ref(v___x_2416_);
lean_dec_ref(v_env_2412_);
lean_dec(v_declHint_2408_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_msg_2407_);
return v___x_2418_;
}
else
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v_c_2424_; lean_object* v___x_2425_; 
v___x_2419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2420_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2421_ = l_Lean_Options_empty;
v___x_2422_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2416_);
lean_ctor_set(v___x_2422_, 1, v___x_2419_);
lean_ctor_set(v___x_2422_, 2, v___x_2420_);
lean_ctor_set(v___x_2422_, 3, v___x_2421_);
lean_inc(v_declHint_2408_);
v___x_2423_ = l_Lean_MessageData_ofConstName(v_declHint_2408_, v___x_2413_);
v_c_2424_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2424_, 0, v___x_2422_);
lean_ctor_set(v_c_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2412_, v_declHint_2408_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_dec_ref(v_env_2412_);
lean_dec(v_declHint_2408_);
v___x_2426_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2426_);
lean_ctor_set(v___x_2427_, 1, v_c_2424_);
v___x_2428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = l_Lean_MessageData_note(v___x_2429_);
v___x_2431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2431_, 0, v_msg_2407_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2431_);
return v___x_2432_;
}
else
{
lean_object* v_val_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2468_; 
v_val_2433_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2435_ = v___x_2425_;
v_isShared_2436_ = v_isSharedCheck_2468_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_val_2433_);
lean_dec(v___x_2425_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2468_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v_mod_2440_; uint8_t v___x_2441_; 
v___x_2437_ = lean_box(0);
v___x_2438_ = l_Lean_Environment_header(v_env_2412_);
lean_dec_ref(v_env_2412_);
v___x_2439_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2438_);
v_mod_2440_ = lean_array_get(v___x_2437_, v___x_2439_, v_val_2433_);
lean_dec(v_val_2433_);
lean_dec_ref(v___x_2439_);
v___x_2441_ = l_Lean_isPrivateName(v_declHint_2408_);
lean_dec(v_declHint_2408_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2442_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v_c_2424_);
v___x_2444_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2443_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = l_Lean_MessageData_ofName(v_mod_2440_);
v___x_2447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2445_);
lean_ctor_set(v___x_2447_, 1, v___x_2446_);
v___x_2448_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2447_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = l_Lean_MessageData_note(v___x_2449_);
v___x_2451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2451_, 0, v_msg_2407_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2451_);
v___x_2453_ = v___x_2435_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2455_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2455_);
lean_ctor_set(v___x_2456_, 1, v_c_2424_);
v___x_2457_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = l_Lean_MessageData_ofName(v_mod_2440_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2458_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_MessageData_note(v___x_2462_);
v___x_2464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_msg_2407_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2464_);
v___x_2466_ = v___x_2435_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2469_; 
lean_dec_ref(v_env_2412_);
lean_dec(v_declHint_2408_);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v_msg_2407_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2470_, lean_object* v_declHint_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2470_, v_declHint_2471_, v___y_2472_);
lean_dec(v___y_2472_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2475_, lean_object* v_declHint_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v___x_2483_; lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2493_; 
v___x_2483_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2475_, v_declHint_2476_, v___y_2481_);
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2493_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2488_ = l_Lean_unknownIdentifierMessageTag;
v___x_2489_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v_a_2484_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2489_);
v___x_2491_ = v___x_2486_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2494_, lean_object* v_declHint_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2494_, v_declHint_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_ref_2509_; lean_object* v___x_2510_; lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2519_; 
v_ref_2509_ = lean_ctor_get(v___y_2506_, 5);
v___x_2510_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2519_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2517_; 
lean_inc(v_ref_2509_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v_ref_2509_);
lean_ctor_set(v___x_2515_, 1, v_a_2511_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set_tag(v___x_2513_, 1);
lean_ctor_set(v___x_2513_, 0, v___x_2515_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___x_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2527_, lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_fileName_2535_; lean_object* v_fileMap_2536_; lean_object* v_options_2537_; lean_object* v_currRecDepth_2538_; lean_object* v_maxRecDepth_2539_; lean_object* v_ref_2540_; lean_object* v_currNamespace_2541_; lean_object* v_openDecls_2542_; lean_object* v_initHeartbeats_2543_; lean_object* v_maxHeartbeats_2544_; lean_object* v_quotContext_2545_; lean_object* v_currMacroScope_2546_; uint8_t v_diag_2547_; lean_object* v_cancelTk_x3f_2548_; uint8_t v_suppressElabErrors_2549_; lean_object* v_inheritedTraceOptions_2550_; lean_object* v_ref_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v_fileName_2535_ = lean_ctor_get(v___y_2532_, 0);
v_fileMap_2536_ = lean_ctor_get(v___y_2532_, 1);
v_options_2537_ = lean_ctor_get(v___y_2532_, 2);
v_currRecDepth_2538_ = lean_ctor_get(v___y_2532_, 3);
v_maxRecDepth_2539_ = lean_ctor_get(v___y_2532_, 4);
v_ref_2540_ = lean_ctor_get(v___y_2532_, 5);
v_currNamespace_2541_ = lean_ctor_get(v___y_2532_, 6);
v_openDecls_2542_ = lean_ctor_get(v___y_2532_, 7);
v_initHeartbeats_2543_ = lean_ctor_get(v___y_2532_, 8);
v_maxHeartbeats_2544_ = lean_ctor_get(v___y_2532_, 9);
v_quotContext_2545_ = lean_ctor_get(v___y_2532_, 10);
v_currMacroScope_2546_ = lean_ctor_get(v___y_2532_, 11);
v_diag_2547_ = lean_ctor_get_uint8(v___y_2532_, sizeof(void*)*14);
v_cancelTk_x3f_2548_ = lean_ctor_get(v___y_2532_, 12);
v_suppressElabErrors_2549_ = lean_ctor_get_uint8(v___y_2532_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2550_ = lean_ctor_get(v___y_2532_, 13);
v_ref_2551_ = l_Lean_replaceRef(v_ref_2527_, v_ref_2540_);
lean_inc_ref(v_inheritedTraceOptions_2550_);
lean_inc(v_cancelTk_x3f_2548_);
lean_inc(v_currMacroScope_2546_);
lean_inc(v_quotContext_2545_);
lean_inc(v_maxHeartbeats_2544_);
lean_inc(v_initHeartbeats_2543_);
lean_inc(v_openDecls_2542_);
lean_inc(v_currNamespace_2541_);
lean_inc(v_maxRecDepth_2539_);
lean_inc(v_currRecDepth_2538_);
lean_inc_ref(v_options_2537_);
lean_inc_ref(v_fileMap_2536_);
lean_inc_ref(v_fileName_2535_);
v___x_2552_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2552_, 0, v_fileName_2535_);
lean_ctor_set(v___x_2552_, 1, v_fileMap_2536_);
lean_ctor_set(v___x_2552_, 2, v_options_2537_);
lean_ctor_set(v___x_2552_, 3, v_currRecDepth_2538_);
lean_ctor_set(v___x_2552_, 4, v_maxRecDepth_2539_);
lean_ctor_set(v___x_2552_, 5, v_ref_2551_);
lean_ctor_set(v___x_2552_, 6, v_currNamespace_2541_);
lean_ctor_set(v___x_2552_, 7, v_openDecls_2542_);
lean_ctor_set(v___x_2552_, 8, v_initHeartbeats_2543_);
lean_ctor_set(v___x_2552_, 9, v_maxHeartbeats_2544_);
lean_ctor_set(v___x_2552_, 10, v_quotContext_2545_);
lean_ctor_set(v___x_2552_, 11, v_currMacroScope_2546_);
lean_ctor_set(v___x_2552_, 12, v_cancelTk_x3f_2548_);
lean_ctor_set(v___x_2552_, 13, v_inheritedTraceOptions_2550_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*14, v_diag_2547_);
lean_ctor_set_uint8(v___x_2552_, sizeof(void*)*14 + 1, v_suppressElabErrors_2549_);
v___x_2553_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2528_, v___y_2530_, v___y_2531_, v___x_2552_, v___y_2533_);
lean_dec_ref(v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2554_, lean_object* v_msg_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2554_, v_msg_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2559_);
lean_dec(v___y_2558_);
lean_dec_ref(v___y_2557_);
lean_dec(v___y_2556_);
lean_dec(v_ref_2554_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2563_, lean_object* v_msg_2564_, lean_object* v_declHint_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v___x_2572_; lean_object* v_a_2573_; lean_object* v___x_2574_; 
v___x_2572_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2564_, v_declHint_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref(v___x_2572_);
v___x_2574_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2563_, v_a_2573_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2575_, lean_object* v_msg_2576_, lean_object* v_declHint_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2575_, v_msg_2576_, v_declHint_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec(v_ref_2575_);
return v_res_2584_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2586_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2587_ = l_Lean_stringToMessageData(v___x_2586_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2590_ = l_Lean_stringToMessageData(v___x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2591_, lean_object* v_constName_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; uint8_t v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2599_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2600_ = 0;
lean_inc(v_constName_2592_);
v___x_2601_ = l_Lean_MessageData_ofConstName(v_constName_2592_, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2599_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2591_, v___x_2604_, v_constName_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2606_, lean_object* v_constName_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2606_, v_constName_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec(v_ref_2606_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_ref_2622_; lean_object* v___x_2623_; 
v_ref_2622_ = lean_ctor_get(v___y_2619_, 5);
v___x_2623_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2622_, v_constName_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; lean_object* v_env_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; 
v___x_2639_ = lean_st_ref_get(v___y_2637_);
v_env_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc_ref(v_env_2640_);
lean_dec(v___x_2639_);
v___x_2641_ = 0;
lean_inc(v_constName_2632_);
v___x_2642_ = l_Lean_Environment_find_x3f(v_env_2640_, v_constName_2632_, v___x_2641_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v___x_2643_; 
v___x_2643_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2643_;
}
else
{
lean_object* v_val_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_constName_2632_);
v_val_2644_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___x_2642_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_val_2644_);
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
lean_ctor_set_tag(v___x_2646_, 0);
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_val_2644_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
return v_res_2659_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2664_ = lean_unsigned_to_nat(53u);
v___x_2665_ = lean_unsigned_to_nat(62u);
v___x_2666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2667_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2668_ = l_mkPanicMessageWithDecl(v___x_2667_, v___x_2666_, v___x_2665_, v___x_2664_, v___x_2663_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2669_, size_t v_i_2670_, lean_object* v_bs_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_usize_dec_lt(v_i_2670_, v_sz_2669_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2679_, 0, v_bs_2671_);
return v___x_2679_;
}
else
{
lean_object* v_v_2680_; lean_object* v___x_2681_; 
v_v_2680_ = lean_array_uget_borrowed(v_bs_2671_, v_i_2670_);
lean_inc(v_v_2680_);
v___x_2681_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2680_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v_bs_x27_2684_; lean_object* v_a_2686_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref(v___x_2681_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v_bs_x27_2684_ = lean_array_uset(v_bs_2671_, v_i_2670_, v___x_2683_);
if (lean_obj_tag(v_a_2682_) == 6)
{
lean_object* v_val_2691_; lean_object* v_numFields_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; 
v_val_2691_ = lean_ctor_get(v_a_2682_, 0);
lean_inc_ref(v_val_2691_);
lean_dec_ref(v_a_2682_);
v_numFields_2692_ = lean_ctor_get(v_val_2691_, 4);
lean_inc(v_numFields_2692_);
lean_dec_ref(v_val_2691_);
v___x_2693_ = 0;
v___x_2694_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2694_, 0, v_numFields_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2683_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*2, v___x_2693_);
v_a_2686_ = v___x_2694_;
goto v___jp_2685_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec(v_a_2682_);
v___x_2695_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2696_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2695_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
v_a_2686_ = v_a_2697_;
goto v___jp_2685_;
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2705_; 
lean_dec_ref(v_bs_x27_2684_);
v_a_2698_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2700_ = v___x_2696_;
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2696_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2705_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2703_; 
if (v_isShared_2701_ == 0)
{
v___x_2703_ = v___x_2700_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
v___jp_2685_:
{
size_t v___x_2687_; size_t v___x_2688_; lean_object* v___x_2689_; 
v___x_2687_ = ((size_t)1ULL);
v___x_2688_ = lean_usize_add(v_i_2670_, v___x_2687_);
v___x_2689_ = lean_array_uset(v_bs_x27_2684_, v_i_2670_, v_a_2686_);
v_i_2670_ = v___x_2688_;
v_bs_2671_ = v___x_2689_;
goto _start;
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_bs_2671_);
v_a_2706_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2681_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2681_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2714_, lean_object* v_i_2715_, lean_object* v_bs_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
size_t v_sz_boxed_2723_; size_t v_i_boxed_2724_; lean_object* v_res_2725_; 
v_sz_boxed_2723_ = lean_unbox_usize(v_sz_2714_);
lean_dec(v_sz_2714_);
v_i_boxed_2724_ = lean_unbox_usize(v_i_2715_);
lean_dec(v_i_2715_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2723_, v_i_boxed_2724_, v_bs_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
return v_res_2725_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2726_ = lean_box(0);
v___x_2727_ = lean_unsigned_to_nat(16u);
v___x_2728_ = lean_mk_array(v___x_2727_, v___x_2726_);
return v___x_2728_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2729_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2730_ = lean_unsigned_to_nat(0u);
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
lean_ctor_set(v___x_2731_, 1, v___x_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2734_, uint8_t v_alsoCasesOn_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
uint8_t v___x_2745_; 
v___x_2745_ = l_Lean_Expr_isApp(v_e_2734_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_dec_ref(v_e_2734_);
v___x_2746_ = lean_box(0);
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
return v___x_2747_;
}
else
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Lean_Expr_getAppFn(v_e_2734_);
if (lean_obj_tag(v___x_2748_) == 4)
{
lean_object* v_declName_2749_; lean_object* v_us_2750_; lean_object* v___x_2751_; lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2906_; 
v_declName_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc_n(v_declName_2749_, 2);
v_us_2750_ = lean_ctor_get(v___x_2748_, 1);
lean_inc(v_us_2750_);
lean_dec_ref(v___x_2748_);
v___x_2751_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2749_, v___y_2740_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2754_ = v___x_2751_;
v_isShared_2755_ = v_isSharedCheck_2906_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2751_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2906_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
if (lean_obj_tag(v_a_2752_) == 1)
{
lean_object* v_val_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2798_; 
v_val_2756_ = lean_ctor_get(v_a_2752_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_a_2752_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2758_ = v_a_2752_;
v_isShared_2759_ = v_isSharedCheck_2798_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_val_2756_);
lean_dec(v_a_2752_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2798_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v_dummy_2760_; lean_object* v_nargs_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v_args_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_dummy_2760_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2761_ = l_Lean_Expr_getAppNumArgs(v_e_2734_);
lean_inc(v_nargs_2761_);
v___x_2762_ = lean_mk_array(v_nargs_2761_, v_dummy_2760_);
v___x_2763_ = lean_unsigned_to_nat(1u);
v___x_2764_ = lean_nat_sub(v_nargs_2761_, v___x_2763_);
lean_dec(v_nargs_2761_);
v_args_2765_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2734_, v___x_2762_, v___x_2764_);
v___x_2766_ = lean_array_get_size(v_args_2765_);
v___x_2767_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2756_);
v___x_2768_ = lean_nat_dec_lt(v___x_2766_, v___x_2767_);
lean_dec(v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v_numParams_2769_; lean_object* v_numDiscrs_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2789_; 
v_numParams_2769_ = lean_ctor_get(v_val_2756_, 0);
v_numDiscrs_2770_ = lean_ctor_get(v_val_2756_, 1);
v___x_2771_ = lean_array_mk(v_us_2750_);
v___x_2772_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2769_);
v___x_2773_ = l_Array_extract___redArg(v_args_2765_, v___x_2772_, v_numParams_2769_);
v___x_2774_ = l_Lean_instInhabitedExpr;
v___x_2775_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2756_);
v___x_2776_ = lean_array_get(v___x_2774_, v_args_2765_, v___x_2775_);
lean_dec(v___x_2775_);
v___x_2777_ = lean_nat_add(v_numParams_2769_, v___x_2763_);
v___x_2778_ = lean_nat_add(v___x_2777_, v_numDiscrs_2770_);
lean_inc(v___x_2778_);
lean_inc_ref_n(v_args_2765_, 2);
v___x_2779_ = l_Array_toSubarray___redArg(v_args_2765_, v___x_2777_, v___x_2778_);
v___x_2780_ = l_Subarray_copy___redArg(v___x_2779_);
v___x_2781_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2756_);
v___x_2782_ = lean_nat_add(v___x_2778_, v___x_2781_);
lean_dec(v___x_2781_);
lean_inc(v___x_2782_);
v___x_2783_ = l_Array_toSubarray___redArg(v_args_2765_, v___x_2778_, v___x_2782_);
v___x_2784_ = l_Subarray_copy___redArg(v___x_2783_);
v___x_2785_ = l_Array_toSubarray___redArg(v_args_2765_, v___x_2782_, v___x_2766_);
v___x_2786_ = l_Subarray_copy___redArg(v___x_2785_);
v___x_2787_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2787_, 0, v_val_2756_);
lean_ctor_set(v___x_2787_, 1, v_declName_2749_);
lean_ctor_set(v___x_2787_, 2, v___x_2771_);
lean_ctor_set(v___x_2787_, 3, v___x_2773_);
lean_ctor_set(v___x_2787_, 4, v___x_2776_);
lean_ctor_set(v___x_2787_, 5, v___x_2780_);
lean_ctor_set(v___x_2787_, 6, v___x_2784_);
lean_ctor_set(v___x_2787_, 7, v___x_2786_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2787_);
v___x_2789_ = v___x_2758_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2787_);
v___x_2789_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
lean_object* v___x_2791_; 
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2789_);
v___x_2791_ = v___x_2754_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2789_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
lean_dec_ref(v_args_2765_);
lean_del_object(v___x_2758_);
lean_dec(v_val_2756_);
lean_dec(v_us_2750_);
lean_dec(v_declName_2749_);
v___x_2794_ = lean_box(0);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2794_);
v___x_2796_ = v___x_2754_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
else
{
lean_object* v___x_2799_; 
lean_del_object(v___x_2754_);
lean_dec(v_a_2752_);
v___x_2799_ = lean_st_ref_get(v___y_2740_);
if (v_alsoCasesOn_2735_ == 0)
{
lean_dec(v___x_2799_);
lean_dec(v_us_2750_);
lean_dec(v_declName_2749_);
lean_dec_ref(v_e_2734_);
goto v___jp_2742_;
}
else
{
lean_object* v_env_2800_; uint8_t v___x_2801_; 
v_env_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc_ref(v_env_2800_);
lean_dec(v___x_2799_);
lean_inc(v_declName_2749_);
v___x_2801_ = l_Lean_isCasesOnRecursor(v_env_2800_, v_declName_2749_);
if (v___x_2801_ == 0)
{
lean_dec(v_us_2750_);
lean_dec(v_declName_2749_);
lean_dec_ref(v_e_2734_);
goto v___jp_2742_;
}
else
{
lean_object* v_indName_2802_; lean_object* v___x_2803_; 
v_indName_2802_ = l_Lean_Name_getPrefix(v_declName_2749_);
v___x_2803_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2802_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2897_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2806_ = v___x_2803_;
v_isShared_2807_ = v_isSharedCheck_2897_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2803_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2897_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
if (lean_obj_tag(v_a_2804_) == 5)
{
lean_object* v_val_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2892_; 
v_val_2808_ = lean_ctor_get(v_a_2804_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v_a_2804_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2810_ = v_a_2804_;
v_isShared_2811_ = v_isSharedCheck_2892_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_val_2808_);
lean_dec(v_a_2804_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2892_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v_toConstantVal_2812_; lean_object* v_numParams_2813_; lean_object* v_numIndices_2814_; lean_object* v_ctors_2815_; lean_object* v_nargs_2816_; lean_object* v_dummy_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v_args_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_toConstantVal_2812_ = lean_ctor_get(v_val_2808_, 0);
lean_inc_ref(v_toConstantVal_2812_);
v_numParams_2813_ = lean_ctor_get(v_val_2808_, 1);
lean_inc(v_numParams_2813_);
v_numIndices_2814_ = lean_ctor_get(v_val_2808_, 2);
lean_inc(v_numIndices_2814_);
v_ctors_2815_ = lean_ctor_get(v_val_2808_, 4);
lean_inc(v_ctors_2815_);
v_nargs_2816_ = l_Lean_Expr_getAppNumArgs(v_e_2734_);
v_dummy_2817_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2816_);
v___x_2818_ = lean_mk_array(v_nargs_2816_, v_dummy_2817_);
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_nat_sub(v_nargs_2816_, v___x_2819_);
lean_dec(v_nargs_2816_);
v_args_2821_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2734_, v___x_2818_, v___x_2820_);
v___x_2822_ = lean_nat_add(v_numParams_2813_, v___x_2819_);
v___x_2823_ = lean_nat_add(v___x_2822_, v_numIndices_2814_);
v___x_2824_ = lean_nat_add(v___x_2823_, v___x_2819_);
lean_dec(v___x_2823_);
v___x_2825_ = l_Lean_InductiveVal_numCtors(v_val_2808_);
lean_dec_ref(v_val_2808_);
v___x_2826_ = lean_nat_add(v___x_2824_, v___x_2825_);
lean_dec(v___x_2825_);
v___x_2827_ = lean_array_get_size(v_args_2821_);
v___x_2828_ = lean_nat_dec_le(v___x_2826_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2831_; 
lean_dec(v___x_2826_);
lean_dec(v___x_2824_);
lean_dec(v___x_2822_);
lean_dec_ref(v_args_2821_);
lean_dec(v_ctors_2815_);
lean_dec(v_numIndices_2814_);
lean_dec(v_numParams_2813_);
lean_dec_ref(v_toConstantVal_2812_);
lean_del_object(v___x_2810_);
lean_dec(v_us_2750_);
lean_dec(v_declName_2749_);
v___x_2829_ = lean_box(0);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2829_);
v___x_2831_ = v___x_2806_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
else
{
lean_object* v___x_2833_; lean_object* v_params_2834_; lean_object* v___x_2835_; lean_object* v_motive_2836_; lean_object* v_discrs_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v_discrInfos_2840_; lean_object* v_alts_2841_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v_lower_2883_; lean_object* v_upper_2884_; uint8_t v___x_2891_; 
lean_del_object(v___x_2806_);
v___x_2833_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2813_);
lean_inc_ref_n(v_args_2821_, 3);
v_params_2834_ = l_Array_toSubarray___redArg(v_args_2821_, v___x_2833_, v_numParams_2813_);
v___x_2835_ = l_Lean_instInhabitedExpr;
v_motive_2836_ = lean_array_get(v___x_2835_, v_args_2821_, v_numParams_2813_);
lean_dec(v_numParams_2813_);
lean_inc(v___x_2824_);
v_discrs_2837_ = l_Array_toSubarray___redArg(v_args_2821_, v___x_2822_, v___x_2824_);
v___x_2838_ = lean_nat_add(v_numIndices_2814_, v___x_2819_);
lean_dec(v_numIndices_2814_);
v___x_2839_ = lean_box(0);
v_discrInfos_2840_ = lean_mk_array(v___x_2838_, v___x_2839_);
lean_inc(v___x_2826_);
v_alts_2841_ = l_Array_toSubarray___redArg(v_args_2821_, v___x_2824_, v___x_2826_);
v___x_2891_ = lean_nat_dec_le(v___x_2826_, v___x_2833_);
if (v___x_2891_ == 0)
{
v_lower_2883_ = v___x_2826_;
v_upper_2884_ = v___x_2827_;
goto v___jp_2882_;
}
else
{
lean_dec(v___x_2826_);
v_lower_2883_ = v___x_2833_;
v_upper_2884_ = v___x_2827_;
goto v___jp_2882_;
}
v___jp_2842_:
{
lean_object* v___x_2845_; size_t v_sz_2846_; size_t v___x_2847_; lean_object* v___x_2848_; 
v___x_2845_ = lean_array_mk(v_ctors_2815_);
v_sz_2846_ = lean_array_size(v___x_2845_);
v___x_2847_ = ((size_t)0ULL);
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2846_, v___x_2847_, v___x_2845_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2873_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2873_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2873_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_start_2853_; lean_object* v_stop_2854_; lean_object* v_start_2855_; lean_object* v_stop_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v_start_2853_ = lean_ctor_get(v_params_2834_, 1);
lean_inc(v_start_2853_);
v_stop_2854_ = lean_ctor_get(v_params_2834_, 2);
lean_inc(v_stop_2854_);
v_start_2855_ = lean_ctor_get(v_discrs_2837_, 1);
lean_inc(v_start_2855_);
v_stop_2856_ = lean_ctor_get(v_discrs_2837_, 2);
lean_inc(v_stop_2856_);
v___x_2857_ = lean_nat_sub(v_stop_2854_, v_start_2853_);
lean_dec(v_start_2853_);
lean_dec(v_stop_2854_);
v___x_2858_ = lean_nat_sub(v_stop_2856_, v_start_2855_);
lean_dec(v_start_2855_);
lean_dec(v_stop_2856_);
v___x_2859_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2860_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2857_);
lean_ctor_set(v___x_2860_, 1, v___x_2858_);
lean_ctor_set(v___x_2860_, 2, v_a_2849_);
lean_ctor_set(v___x_2860_, 3, v___y_2844_);
lean_ctor_set(v___x_2860_, 4, v_discrInfos_2840_);
lean_ctor_set(v___x_2860_, 5, v___x_2859_);
v___x_2861_ = lean_array_mk(v_us_2750_);
v___x_2862_ = l_Subarray_copy___redArg(v_params_2834_);
v___x_2863_ = l_Subarray_copy___redArg(v_discrs_2837_);
v___x_2864_ = l_Subarray_copy___redArg(v_alts_2841_);
v___x_2865_ = l_Subarray_copy___redArg(v___y_2843_);
v___x_2866_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2860_);
lean_ctor_set(v___x_2866_, 1, v_declName_2749_);
lean_ctor_set(v___x_2866_, 2, v___x_2861_);
lean_ctor_set(v___x_2866_, 3, v___x_2862_);
lean_ctor_set(v___x_2866_, 4, v_motive_2836_);
lean_ctor_set(v___x_2866_, 5, v___x_2863_);
lean_ctor_set(v___x_2866_, 6, v___x_2864_);
lean_ctor_set(v___x_2866_, 7, v___x_2865_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 1);
lean_ctor_set(v___x_2810_, 0, v___x_2866_);
v___x_2868_ = v___x_2810_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2870_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2868_);
v___x_2870_ = v___x_2851_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2868_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v_alts_2841_);
lean_dec_ref(v_discrInfos_2840_);
lean_dec_ref(v_discrs_2837_);
lean_dec(v_motive_2836_);
lean_dec_ref(v_params_2834_);
lean_del_object(v___x_2810_);
lean_dec(v_us_2750_);
lean_dec(v_declName_2749_);
v_a_2874_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2848_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2848_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
v___jp_2882_:
{
lean_object* v_levelParams_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v_levelParams_2885_ = lean_ctor_get(v_toConstantVal_2812_, 1);
lean_inc(v_levelParams_2885_);
lean_dec_ref(v_toConstantVal_2812_);
v___x_2886_ = l_Array_toSubarray___redArg(v_args_2821_, v_lower_2883_, v_upper_2884_);
v___x_2887_ = l_List_lengthTR___redArg(v_levelParams_2885_);
lean_dec(v_levelParams_2885_);
v___x_2888_ = l_List_lengthTR___redArg(v_us_2750_);
v___x_2889_ = lean_nat_dec_eq(v___x_2887_, v___x_2888_);
lean_dec(v___x_2888_);
lean_dec(v___x_2887_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2890_; 
v___x_2890_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2843_ = v___x_2886_;
v___y_2844_ = v___x_2890_;
goto v___jp_2842_;
}
else
{
v___y_2843_ = v___x_2886_;
v___y_2844_ = v___x_2839_;
goto v___jp_2842_;
}
}
}
}
}
else
{
lean_object* v___x_2893_; lean_object* v___x_2895_; 
lean_dec(v_a_2804_);
lean_dec(v_us_2750_);
lean_dec(v_declName_2749_);
lean_dec_ref(v_e_2734_);
v___x_2893_ = lean_box(0);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2893_);
v___x_2895_ = v___x_2806_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_us_2750_);
lean_dec(v_declName_2749_);
lean_dec_ref(v_e_2734_);
v_a_2898_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2803_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2803_);
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
}
}
}
else
{
lean_dec_ref(v___x_2748_);
lean_dec_ref(v_e_2734_);
goto v___jp_2742_;
}
}
v___jp_2742_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2907_, lean_object* v_alsoCasesOn_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2915_; lean_object* v_res_2916_; 
v_alsoCasesOn_boxed_2915_ = lean_unbox(v_alsoCasesOn_2908_);
v_res_2916_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2907_, v_alsoCasesOn_boxed_2915_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
if (lean_obj_tag(v_a_2917_) == 0)
{
lean_object* v___x_2919_; 
v___x_2919_ = l_List_reverse___redArg(v_a_2918_);
return v___x_2919_;
}
else
{
lean_object* v_head_2920_; lean_object* v_tail_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2930_; 
v_head_2920_ = lean_ctor_get(v_a_2917_, 0);
v_tail_2921_ = lean_ctor_get(v_a_2917_, 1);
v_isSharedCheck_2930_ = !lean_is_exclusive(v_a_2917_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2923_ = v_a_2917_;
v_isShared_2924_ = v_isSharedCheck_2930_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_tail_2921_);
lean_inc(v_head_2920_);
lean_dec(v_a_2917_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2930_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2925_ = l_Lean_MessageData_ofExpr(v_head_2920_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v_a_2918_);
lean_ctor_set(v___x_2923_, 0, v___x_2925_);
v___x_2927_ = v___x_2923_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_a_2918_);
v___x_2927_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
v_a_2917_ = v_tail_2921_;
v_a_2918_ = v___x_2927_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2931_, lean_object* v_x_2932_){
_start:
{
lean_object* v_fnName_2933_; uint8_t v___x_2934_; 
v_fnName_2933_ = lean_ctor_get(v_x_2932_, 0);
v___x_2934_ = l_Lean_Expr_isConstOf(v_x_2931_, v_fnName_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2935_, lean_object* v_x_2936_){
_start:
{
uint8_t v_res_2937_; lean_object* v_r_2938_; 
v_res_2937_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2935_, v_x_2936_);
lean_dec_ref(v_x_2936_);
lean_dec_ref(v_x_2935_);
v_r_2938_ = lean_box(v_res_2937_);
return v_r_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2939_, lean_object* v_type_2940_, lean_object* v_val_2941_, lean_object* v_k_2942_, uint8_t v_nondep_2943_, uint8_t v_kind_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v___f_2951_; lean_object* v___x_2952_; 
lean_inc(v___y_2945_);
v___f_2951_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2951_, 0, v_k_2942_);
lean_closure_set(v___f_2951_, 1, v___y_2945_);
v___x_2952_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2939_, v_type_2940_, v_val_2941_, v___f_2951_, v_nondep_2943_, v_kind_2944_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2952_) == 0)
{
return v___x_2952_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2961_, lean_object* v_type_2962_, lean_object* v_val_2963_, lean_object* v_k_2964_, lean_object* v_nondep_2965_, lean_object* v_kind_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
uint8_t v_nondep_boxed_2973_; uint8_t v_kind_boxed_2974_; lean_object* v_res_2975_; 
v_nondep_boxed_2973_ = lean_unbox(v_nondep_2965_);
v_kind_boxed_2974_ = lean_unbox(v_kind_2966_);
v_res_2975_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2961_, v_type_2962_, v_val_2963_, v_k_2964_, v_nondep_boxed_2973_, v_kind_boxed_2974_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v___y_2967_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2976_, uint8_t v_usedLetOnly_2977_, lean_object* v_x_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; 
lean_inc(v___y_2983_);
lean_inc_ref(v___y_2982_);
lean_inc(v___y_2981_);
lean_inc_ref(v___y_2980_);
lean_inc(v___y_2979_);
lean_inc_ref(v_x_2978_);
v___x_2985_ = lean_apply_7(v_k_2976_, v_x_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, lean_box(0));
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref(v___x_2985_);
v___x_2987_ = lean_unsigned_to_nat(1u);
v___x_2988_ = lean_mk_empty_array_with_capacity(v___x_2987_);
v___x_2989_ = lean_array_push(v___x_2988_, v_x_2978_);
v___x_2990_ = 0;
v___x_2991_ = 1;
v___x_2992_ = l_Lean_Meta_mkLetFVars(v___x_2989_, v_a_2986_, v_usedLetOnly_2977_, v___x_2990_, v___x_2991_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec_ref(v___x_2989_);
return v___x_2992_;
}
else
{
lean_dec_ref(v_x_2978_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2993_, lean_object* v_usedLetOnly_2994_, lean_object* v_x_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
uint8_t v_usedLetOnly_boxed_3002_; lean_object* v_res_3003_; 
v_usedLetOnly_boxed_3002_ = lean_unbox(v_usedLetOnly_2994_);
v_res_3003_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2993_, v_usedLetOnly_boxed_3002_, v_x_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_3004_, lean_object* v_type_3005_, lean_object* v_val_3006_, lean_object* v_k_3007_, uint8_t v_nondep_3008_, uint8_t v_kind_3009_, uint8_t v_usedLetOnly_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; lean_object* v___f_3018_; lean_object* v___x_3019_; 
v___x_3017_ = lean_box(v_usedLetOnly_3010_);
v___f_3018_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3018_, 0, v_k_3007_);
lean_closure_set(v___f_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3004_, v_type_3005_, v_val_3006_, v___f_3018_, v_nondep_3008_, v_kind_3009_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_3020_, lean_object* v_type_3021_, lean_object* v_val_3022_, lean_object* v_k_3023_, lean_object* v_nondep_3024_, lean_object* v_kind_3025_, lean_object* v_usedLetOnly_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
uint8_t v_nondep_boxed_3033_; uint8_t v_kind_boxed_3034_; uint8_t v_usedLetOnly_boxed_3035_; lean_object* v_res_3036_; 
v_nondep_boxed_3033_ = lean_unbox(v_nondep_3024_);
v_kind_boxed_3034_ = lean_unbox(v_kind_3025_);
v_usedLetOnly_boxed_3035_ = lean_unbox(v_usedLetOnly_3026_);
v_res_3036_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_3020_, v_type_3021_, v_val_3022_, v_k_3023_, v_nondep_boxed_3033_, v_kind_boxed_3034_, v_usedLetOnly_boxed_3035_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3037_, lean_object* v_positions_3038_, lean_object* v_recFnNames_3039_, lean_object* v_containsRecFn_3040_, lean_object* v_below_3041_, size_t v_sz_3042_, size_t v_i_3043_, lean_object* v_bs_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_usize_dec_lt(v_i_3043_, v_sz_3042_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
lean_dec_ref(v_below_3041_);
lean_dec_ref(v_containsRecFn_3040_);
lean_dec_ref(v_recFnNames_3039_);
lean_dec_ref(v_positions_3038_);
lean_dec_ref(v_recArgInfos_3037_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_bs_3044_);
return v___x_3052_;
}
else
{
lean_object* v_v_3053_; lean_object* v___x_3054_; 
v_v_3053_ = lean_array_uget_borrowed(v_bs_3044_, v_i_3043_);
lean_inc_ref(v___y_3048_);
lean_inc(v_v_3053_);
lean_inc_ref(v_below_3041_);
lean_inc_ref(v_containsRecFn_3040_);
lean_inc_ref(v_recFnNames_3039_);
lean_inc_ref(v_positions_3038_);
lean_inc_ref(v_recArgInfos_3037_);
v___x_3054_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3037_, v_positions_3038_, v_recFnNames_3039_, v_containsRecFn_3040_, v_below_3041_, v_v_3053_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3056_; lean_object* v_bs_x27_3057_; size_t v___x_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref(v___x_3054_);
v___x_3056_ = lean_unsigned_to_nat(0u);
v_bs_x27_3057_ = lean_array_uset(v_bs_3044_, v_i_3043_, v___x_3056_);
v___x_3058_ = ((size_t)1ULL);
v___x_3059_ = lean_usize_add(v_i_3043_, v___x_3058_);
v___x_3060_ = lean_array_uset(v_bs_x27_3057_, v_i_3043_, v_a_3055_);
v_i_3043_ = v___x_3059_;
v_bs_3044_ = v___x_3060_;
goto _start;
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec_ref(v_bs_3044_);
lean_dec_ref(v_below_3041_);
lean_dec_ref(v_containsRecFn_3040_);
lean_dec_ref(v_recFnNames_3039_);
lean_dec_ref(v_positions_3038_);
lean_dec_ref(v_recArgInfos_3037_);
v_a_3062_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3054_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3054_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3072_ = l_Lean_stringToMessageData(v___x_3071_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3076_, lean_object* v_positions_3077_, lean_object* v_recFnNames_3078_, lean_object* v_containsRecFn_3079_, lean_object* v_below_3080_, lean_object* v_e_3081_, lean_object* v_x_3082_, lean_object* v_x_3083_, lean_object* v_x_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
if (lean_obj_tag(v_x_3082_) == 5)
{
lean_object* v_fn_3091_; lean_object* v_arg_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v_fn_3091_ = lean_ctor_get(v_x_3082_, 0);
lean_inc_ref(v_fn_3091_);
v_arg_3092_ = lean_ctor_get(v_x_3082_, 1);
lean_inc_ref(v_arg_3092_);
lean_dec_ref(v_x_3082_);
v___x_3093_ = lean_array_set(v_x_3083_, v_x_3084_, v_arg_3092_);
v___x_3094_ = lean_unsigned_to_nat(1u);
v___x_3095_ = lean_nat_sub(v_x_3084_, v___x_3094_);
lean_dec(v_x_3084_);
v_x_3082_ = v_fn_3091_;
v_x_3083_ = v___x_3093_;
v_x_3084_ = v___x_3095_;
goto _start;
}
else
{
lean_object* v___f_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec(v_x_3084_);
lean_inc_ref(v_x_3082_);
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3097_, 0, v_x_3082_);
v___x_3098_ = lean_unsigned_to_nat(0u);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3097_, v_recArgInfos_3076_, v___x_3098_);
if (lean_obj_tag(v___x_3099_) == 1)
{
lean_object* v_val_3100_; lean_object* v___x_3101_; lean_object* v___y_3103_; lean_object* v_recArgPos_3129_; lean_object* v_indGroupInst_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
lean_dec_ref(v_x_3082_);
v_val_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_val_3100_);
lean_dec_ref(v___x_3099_);
v___x_3101_ = lean_array_fget_borrowed(v_recArgInfos_3076_, v_val_3100_);
v_recArgPos_3129_ = lean_ctor_get(v___x_3101_, 2);
v_indGroupInst_3130_ = lean_ctor_get(v___x_3101_, 4);
v___x_3131_ = lean_array_get_size(v_x_3083_);
v___x_3132_ = lean_nat_dec_lt(v_recArgPos_3129_, v___x_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec(v_val_3100_);
lean_dec_ref(v_x_3083_);
lean_dec_ref(v_below_3080_);
lean_dec_ref(v_containsRecFn_3079_);
lean_dec_ref(v_recFnNames_3078_);
lean_dec_ref(v_positions_3077_);
lean_dec_ref(v_recArgInfos_3076_);
v___x_3133_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3134_ = l_Lean_indentExpr(v_e_3081_);
v___x_3135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3133_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
v___x_3136_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3135_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_array_fget_borrowed(v_x_3083_, v_recArgPos_3129_);
lean_inc_ref(v___y_3088_);
lean_inc(v___x_3137_);
lean_inc_ref(v_below_3080_);
lean_inc_ref(v_containsRecFn_3079_);
lean_inc_ref(v_recFnNames_3078_);
lean_inc_ref(v_positions_3077_);
lean_inc_ref(v_recArgInfos_3076_);
v___x_3138_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3076_, v_positions_3077_, v_recFnNames_3078_, v_containsRecFn_3079_, v_below_3080_, v___x_3137_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v_params_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3138_);
v_params_3140_ = lean_ctor_get(v_indGroupInst_3130_, 2);
v___x_3141_ = lean_array_get_size(v_params_3140_);
lean_inc_ref(v_positions_3077_);
lean_inc_ref(v_below_3080_);
v___x_3142_ = l_Lean_Elab_Structural_toBelow(v_below_3080_, v___x_3141_, v_positions_3077_, v_val_3100_, v_a_3139_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_dec_ref(v_e_3081_);
v___y_3103_ = v___x_3142_;
goto v___jp_3102_;
}
else
{
lean_object* v_a_3143_; uint8_t v___y_3145_; uint8_t v___x_3150_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
v___x_3150_ = l_Lean_Exception_isInterrupt(v_a_3143_);
if (v___x_3150_ == 0)
{
uint8_t v___x_3151_; 
v___x_3151_ = l_Lean_Exception_isRuntime(v_a_3143_);
v___y_3145_ = v___x_3151_;
goto v___jp_3144_;
}
else
{
lean_dec(v_a_3143_);
v___y_3145_ = v___x_3150_;
goto v___jp_3144_;
}
v___jp_3144_:
{
if (v___y_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec_ref(v___x_3142_);
v___x_3146_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3147_ = l_Lean_indentExpr(v_e_3081_);
v___x_3148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3146_);
lean_ctor_set(v___x_3148_, 1, v___x_3147_);
v___x_3149_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3148_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
v___y_3103_ = v___x_3149_;
goto v___jp_3102_;
}
else
{
lean_dec_ref(v_e_3081_);
v___y_3103_ = v___x_3142_;
goto v___jp_3102_;
}
}
}
}
else
{
lean_dec(v_val_3100_);
lean_dec_ref(v_x_3083_);
lean_dec_ref(v_e_3081_);
lean_dec_ref(v_below_3080_);
lean_dec_ref(v_containsRecFn_3079_);
lean_dec_ref(v_recFnNames_3078_);
lean_dec_ref(v_positions_3077_);
lean_dec_ref(v_recArgInfos_3076_);
return v___x_3138_;
}
}
v___jp_3102_:
{
if (lean_obj_tag(v___y_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v_fixedParamPerm_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v_snd_3108_; size_t v_sz_3109_; size_t v___x_3110_; lean_object* v___x_3111_; 
v_a_3104_ = lean_ctor_get(v___y_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref(v___y_3103_);
v_fixedParamPerm_3105_ = lean_ctor_get(v___x_3101_, 1);
v___x_3106_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3105_, v_x_3083_);
lean_dec_ref(v_x_3083_);
lean_inc(v___x_3101_);
v___x_3107_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3101_, v___x_3106_);
v_snd_3108_ = lean_ctor_get(v___x_3107_, 1);
lean_inc(v_snd_3108_);
lean_dec_ref(v___x_3107_);
v_sz_3109_ = lean_array_size(v_snd_3108_);
v___x_3110_ = ((size_t)0ULL);
v___x_3111_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3076_, v_positions_3077_, v_recFnNames_3078_, v_containsRecFn_3079_, v_below_3080_, v_sz_3109_, v___x_3110_, v_snd_3108_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3120_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3114_ = v___x_3111_;
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3111_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3120_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = l_Lean_mkAppN(v_a_3104_, v_a_3112_);
lean_dec(v_a_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3118_ = v___x_3114_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
else
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3128_; 
lean_dec(v_a_3104_);
v_a_3121_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3123_ = v___x_3111_;
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3111_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3128_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3124_ == 0)
{
v___x_3126_ = v___x_3123_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_dec_ref(v_x_3083_);
lean_dec_ref(v_below_3080_);
lean_dec_ref(v_containsRecFn_3079_);
lean_dec_ref(v_recFnNames_3078_);
lean_dec_ref(v_positions_3077_);
lean_dec_ref(v_recArgInfos_3076_);
return v___y_3103_;
}
}
}
else
{
lean_object* v___x_3152_; 
lean_dec(v___x_3099_);
lean_dec_ref(v_e_3081_);
lean_inc_ref(v___y_3088_);
lean_inc_ref(v_below_3080_);
lean_inc_ref(v_containsRecFn_3079_);
lean_inc_ref(v_recFnNames_3078_);
lean_inc_ref(v_positions_3077_);
lean_inc_ref(v_recArgInfos_3076_);
v___x_3152_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3076_, v_positions_3077_, v_recFnNames_3078_, v_containsRecFn_3079_, v_below_3080_, v_x_3082_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; size_t v_sz_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref(v___x_3152_);
v_sz_3154_ = lean_array_size(v_x_3083_);
v___x_3155_ = ((size_t)0ULL);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3076_, v_positions_3077_, v_recFnNames_3078_, v_containsRecFn_3079_, v_below_3080_, v_sz_3154_, v___x_3155_, v_x_3083_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3165_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3165_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3165_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; lean_object* v___x_3163_; 
v___x_3161_ = l_Lean_mkAppN(v_a_3153_, v_a_3157_);
lean_dec(v_a_3157_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v___x_3161_);
v___x_3163_ = v___x_3159_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_a_3153_);
v_a_3166_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3156_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3156_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
else
{
lean_dec_ref(v_x_3083_);
lean_dec_ref(v_below_3080_);
lean_dec_ref(v_containsRecFn_3079_);
lean_dec_ref(v_recFnNames_3078_);
lean_dec_ref(v_positions_3077_);
lean_dec_ref(v_recArgInfos_3076_);
return v___x_3152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3174_, lean_object* v_recArgInfos_3175_, lean_object* v_positions_3176_, lean_object* v_recFnNames_3177_, lean_object* v_containsRecFn_3178_, lean_object* v_below_3179_, uint8_t v___x_3180_, uint8_t v_a_3181_, lean_object* v_x_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_expr_instantiate1(v_body_3174_, v_x_3182_);
lean_inc_ref(v___y_3186_);
v___x_3190_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3175_, v_positions_3176_, v_recFnNames_3177_, v_containsRecFn_3178_, v_below_3179_, v___x_3189_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; lean_object* v___x_3196_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___x_3190_);
v___x_3192_ = lean_unsigned_to_nat(1u);
v___x_3193_ = lean_mk_empty_array_with_capacity(v___x_3192_);
v___x_3194_ = lean_array_push(v___x_3193_, v_x_3182_);
v___x_3195_ = 1;
v___x_3196_ = l_Lean_Meta_mkLambdaFVars(v___x_3194_, v_a_3191_, v___x_3180_, v_a_3181_, v___x_3180_, v_a_3181_, v___x_3195_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec_ref(v___x_3194_);
return v___x_3196_;
}
else
{
lean_dec_ref(v_x_3182_);
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3197_, lean_object* v_recArgInfos_3198_, lean_object* v_positions_3199_, lean_object* v_recFnNames_3200_, lean_object* v_containsRecFn_3201_, lean_object* v_below_3202_, lean_object* v___x_3203_, lean_object* v_a_3204_, lean_object* v_x_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___x_32831__boxed_3212_; uint8_t v_a_32832__boxed_3213_; lean_object* v_res_3214_; 
v___x_32831__boxed_3212_ = lean_unbox(v___x_3203_);
v_a_32832__boxed_3213_ = lean_unbox(v_a_3204_);
v_res_3214_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3197_, v_recArgInfos_3198_, v_positions_3199_, v_recFnNames_3200_, v_containsRecFn_3201_, v_below_3202_, v___x_32831__boxed_3212_, v_a_32832__boxed_3213_, v_x_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v___y_3206_);
lean_dec_ref(v_body_3197_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3215_, lean_object* v_recArgInfos_3216_, lean_object* v_positions_3217_, lean_object* v_recFnNames_3218_, lean_object* v_containsRecFn_3219_, lean_object* v_below_3220_, uint8_t v___x_3221_, uint8_t v_a_3222_, lean_object* v_x_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_expr_instantiate1(v_body_3215_, v_x_3223_);
lean_inc_ref(v___y_3227_);
v___x_3231_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3216_, v_positions_3217_, v_recFnNames_3218_, v_containsRecFn_3219_, v_below_3220_, v___x_3230_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; uint8_t v___x_3236_; lean_object* v___x_3237_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = lean_mk_empty_array_with_capacity(v___x_3233_);
v___x_3235_ = lean_array_push(v___x_3234_, v_x_3223_);
v___x_3236_ = 1;
v___x_3237_ = l_Lean_Meta_mkForallFVars(v___x_3235_, v_a_3232_, v___x_3221_, v_a_3222_, v_a_3222_, v___x_3236_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec_ref(v___x_3235_);
return v___x_3237_;
}
else
{
lean_dec_ref(v_x_3223_);
return v___x_3231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3238_, lean_object* v_recArgInfos_3239_, lean_object* v_positions_3240_, lean_object* v_recFnNames_3241_, lean_object* v_containsRecFn_3242_, lean_object* v_below_3243_, lean_object* v___x_3244_, lean_object* v_a_3245_, lean_object* v_x_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
uint8_t v___x_32849__boxed_3253_; uint8_t v_a_32850__boxed_3254_; lean_object* v_res_3255_; 
v___x_32849__boxed_3253_ = lean_unbox(v___x_3244_);
v_a_32850__boxed_3254_ = lean_unbox(v_a_3245_);
v_res_3255_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3238_, v_recArgInfos_3239_, v_positions_3240_, v_recFnNames_3241_, v_containsRecFn_3242_, v_below_3243_, v___x_32849__boxed_3253_, v_a_32850__boxed_3254_, v_x_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v_body_3238_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3256_, lean_object* v_recArgInfos_3257_, lean_object* v_positions_3258_, lean_object* v_recFnNames_3259_, lean_object* v_containsRecFn_3260_, lean_object* v_below_3261_, lean_object* v_x_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3256_, v_recArgInfos_3257_, v_positions_3258_, v_recFnNames_3259_, v_containsRecFn_3260_, v_below_3261_, v_x_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v_x_3262_);
lean_dec_ref(v_body_3256_);
return v_res_3269_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3274_ = l_Lean_stringToMessageData(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3277_ = l_Lean_stringToMessageData(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3280_ = l_Lean_stringToMessageData(v___x_3279_);
return v___x_3280_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3283_ = l_Lean_stringToMessageData(v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v_b_3284_, lean_object* v_recArgInfos_3285_, lean_object* v_positions_3286_, lean_object* v_recFnNames_3287_, lean_object* v_containsRecFn_3288_, uint8_t v___x_3289_, uint8_t v_a_3290_, lean_object* v___x_3291_, lean_object* v_a_3292_, lean_object* v_e_3293_, lean_object* v___x_3294_, lean_object* v_xs_3295_, lean_object* v_altBody_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v_options_3339_; uint8_t v_hasTrace_3340_; 
v_options_3339_ = lean_ctor_get(v___y_3300_, 2);
v_hasTrace_3340_ = lean_ctor_get_uint8(v_options_3339_, sizeof(void*)*1);
if (v_hasTrace_3340_ == 0)
{
lean_dec(v___x_3294_);
v___y_3316_ = v___y_3297_;
v___y_3317_ = v___y_3298_;
v___y_3318_ = v___y_3299_;
v___y_3319_ = v___y_3300_;
v___y_3320_ = v___y_3301_;
goto v___jp_3315_;
}
else
{
lean_object* v_inheritedTraceOptions_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v_inheritedTraceOptions_3341_ = lean_ctor_get(v___y_3300_, 13);
v___x_3342_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3294_);
v___x_3343_ = l_Lean_Name_append(v___x_3342_, v___x_3294_);
v___x_3344_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3341_, v_options_3339_, v___x_3343_);
lean_dec(v___x_3343_);
if (v___x_3344_ == 0)
{
lean_dec(v___x_3294_);
v___y_3316_ = v___y_3297_;
v___y_3317_ = v___y_3298_;
v___y_3318_ = v___y_3299_;
v___y_3319_ = v___y_3300_;
v___y_3320_ = v___y_3301_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3345_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3284_);
v___x_3346_ = l_Nat_reprFast(v_b_3284_);
v___x_3347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
v___x_3348_ = l_Lean_MessageData_ofFormat(v___x_3347_);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3345_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
lean_inc_ref(v_xs_3295_);
v___x_3352_ = lean_array_to_list(v_xs_3295_);
v___x_3353_ = lean_box(0);
v___x_3354_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3352_, v___x_3353_);
v___x_3355_ = l_Lean_MessageData_ofList(v___x_3354_);
v___x_3356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3351_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3294_, v___x_3356_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_dec_ref(v___x_3357_);
v___y_3316_ = v___y_3297_;
v___y_3317_ = v___y_3298_;
v___y_3318_ = v___y_3299_;
v___y_3319_ = v___y_3300_;
v___y_3320_ = v___y_3301_;
goto v___jp_3315_;
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec_ref(v_altBody_3296_);
lean_dec_ref(v_xs_3295_);
lean_dec_ref(v_e_3293_);
lean_dec_ref(v_a_3292_);
lean_dec_ref(v_containsRecFn_3288_);
lean_dec_ref(v_recFnNames_3287_);
lean_dec_ref(v_positions_3286_);
lean_dec_ref(v_recArgInfos_3285_);
lean_dec(v_b_3284_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
}
v___jp_3303_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3309_ = l_Lean_instInhabitedExpr;
v___x_3310_ = lean_array_get_borrowed(v___x_3309_, v_xs_3295_, v_b_3284_);
lean_dec(v_b_3284_);
lean_inc_ref(v___y_3307_);
lean_inc(v___x_3310_);
v___x_3311_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3285_, v_positions_3286_, v_recFnNames_3287_, v_containsRecFn_3288_, v___x_3310_, v_altBody_3296_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; uint8_t v___x_3313_; lean_object* v___x_3314_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = 1;
v___x_3314_ = l_Lean_Meta_mkLambdaFVars(v_xs_3295_, v_a_3312_, v___x_3289_, v_a_3290_, v___x_3289_, v_a_3290_, v___x_3313_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec_ref(v_xs_3295_);
return v___x_3314_;
}
else
{
lean_dec_ref(v_xs_3295_);
return v___x_3311_;
}
}
v___jp_3315_:
{
lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = lean_array_get_size(v_xs_3295_);
v___x_3322_ = lean_nat_dec_eq(v___x_3321_, v___x_3291_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec_ref(v_altBody_3296_);
lean_dec_ref(v_xs_3295_);
lean_dec_ref(v_containsRecFn_3288_);
lean_dec_ref(v_recFnNames_3287_);
lean_dec_ref(v_positions_3286_);
lean_dec_ref(v_recArgInfos_3285_);
lean_dec(v_b_3284_);
v___x_3323_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3324_ = l_Lean_indentExpr(v_a_3292_);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3323_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3325_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = l_Lean_indentExpr(v_e_3293_);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3329_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
else
{
lean_dec_ref(v_e_3293_);
lean_dec_ref(v_a_3292_);
v___y_3304_ = v___y_3316_;
v___y_3305_ = v___y_3317_;
v___y_3306_ = v___y_3318_;
v___y_3307_ = v___y_3319_;
v___y_3308_ = v___y_3320_;
goto v___jp_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v_b_3366_ = _args[0];
lean_object* v_recArgInfos_3367_ = _args[1];
lean_object* v_positions_3368_ = _args[2];
lean_object* v_recFnNames_3369_ = _args[3];
lean_object* v_containsRecFn_3370_ = _args[4];
lean_object* v___x_3371_ = _args[5];
lean_object* v_a_3372_ = _args[6];
lean_object* v___x_3373_ = _args[7];
lean_object* v_a_3374_ = _args[8];
lean_object* v_e_3375_ = _args[9];
lean_object* v___x_3376_ = _args[10];
lean_object* v_xs_3377_ = _args[11];
lean_object* v_altBody_3378_ = _args[12];
lean_object* v___y_3379_ = _args[13];
lean_object* v___y_3380_ = _args[14];
lean_object* v___y_3381_ = _args[15];
lean_object* v___y_3382_ = _args[16];
lean_object* v___y_3383_ = _args[17];
lean_object* v___y_3384_ = _args[18];
_start:
{
uint8_t v___x_32923__boxed_3385_; uint8_t v_a_32924__boxed_3386_; lean_object* v_res_3387_; 
v___x_32923__boxed_3385_ = lean_unbox(v___x_3371_);
v_a_32924__boxed_3386_ = lean_unbox(v_a_3372_);
v_res_3387_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v_b_3366_, v_recArgInfos_3367_, v_positions_3368_, v_recFnNames_3369_, v_containsRecFn_3370_, v___x_32923__boxed_3385_, v_a_32924__boxed_3386_, v___x_3373_, v_a_3374_, v_e_3375_, v___x_3376_, v_xs_3377_, v_altBody_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec(v___x_3373_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3388_, lean_object* v_positions_3389_, lean_object* v_recFnNames_3390_, lean_object* v_containsRecFn_3391_, uint8_t v_a_3392_, lean_object* v_e_3393_, lean_object* v_as_3394_, lean_object* v_bs_3395_, lean_object* v_i_3396_, lean_object* v_cs_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3404_ = lean_array_get_size(v_as_3394_);
v___x_3405_ = lean_nat_dec_lt(v_i_3396_, v___x_3404_);
if (v___x_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_dec(v_i_3396_);
lean_dec_ref(v_e_3393_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v___x_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3406_, 0, v_cs_3397_);
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = lean_array_get_size(v_bs_3395_);
v___x_3408_ = lean_nat_dec_lt(v_i_3396_, v___x_3407_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; 
lean_dec(v_i_3396_);
lean_dec_ref(v_e_3393_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v___x_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3409_, 0, v_cs_3397_);
return v___x_3409_;
}
else
{
uint8_t v___x_3410_; lean_object* v___x_3411_; lean_object* v_a_3412_; lean_object* v_b_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___f_3418_; lean_object* v___x_3419_; 
v___x_3410_ = 0;
v___x_3411_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3412_ = lean_array_fget_borrowed(v_as_3394_, v_i_3396_);
v_b_3413_ = lean_array_fget_borrowed(v_bs_3395_, v_i_3396_);
v___x_3414_ = lean_unsigned_to_nat(1u);
v___x_3415_ = lean_nat_add(v_b_3413_, v___x_3414_);
v___x_3416_ = lean_box(v___x_3410_);
v___x_3417_ = lean_box(v_a_3392_);
lean_inc_ref(v_e_3393_);
lean_inc_n(v_a_3412_, 2);
lean_inc(v___x_3415_);
lean_inc_ref(v_containsRecFn_3391_);
lean_inc_ref(v_recFnNames_3390_);
lean_inc_ref(v_positions_3389_);
lean_inc_ref(v_recArgInfos_3388_);
lean_inc(v_b_3413_);
v___f_3418_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 19, 11);
lean_closure_set(v___f_3418_, 0, v_b_3413_);
lean_closure_set(v___f_3418_, 1, v_recArgInfos_3388_);
lean_closure_set(v___f_3418_, 2, v_positions_3389_);
lean_closure_set(v___f_3418_, 3, v_recFnNames_3390_);
lean_closure_set(v___f_3418_, 4, v_containsRecFn_3391_);
lean_closure_set(v___f_3418_, 5, v___x_3416_);
lean_closure_set(v___f_3418_, 6, v___x_3417_);
lean_closure_set(v___f_3418_, 7, v___x_3415_);
lean_closure_set(v___f_3418_, 8, v_a_3412_);
lean_closure_set(v___f_3418_, 9, v_e_3393_);
lean_closure_set(v___f_3418_, 10, v___x_3411_);
v___x_3419_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3412_, v___x_3415_, v___f_3418_, v___x_3410_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
lean_dec_ref(v___x_3419_);
v___x_3421_ = lean_nat_add(v_i_3396_, v___x_3414_);
lean_dec(v_i_3396_);
v___x_3422_ = lean_array_push(v_cs_3397_, v_a_3420_);
v_i_3396_ = v___x_3421_;
v_cs_3397_ = v___x_3422_;
goto _start;
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_cs_3397_);
lean_dec(v_i_3396_);
lean_dec_ref(v_e_3393_);
lean_dec_ref(v_containsRecFn_3391_);
lean_dec_ref(v_recFnNames_3390_);
lean_dec_ref(v_positions_3389_);
lean_dec_ref(v_recArgInfos_3388_);
v_a_3424_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3419_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3419_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
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
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3441_, lean_object* v_positions_3442_, lean_object* v_recFnNames_3443_, lean_object* v_containsRecFn_3444_, lean_object* v_below_3445_, lean_object* v_e_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_){
_start:
{
lean_object* v_e_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___x_3466_; 
lean_inc_ref(v_containsRecFn_3444_);
lean_inc(v_a_3451_);
lean_inc_ref(v_a_3450_);
lean_inc(v_a_3449_);
lean_inc_ref(v_a_3448_);
lean_inc(v_a_3447_);
lean_inc_ref(v_e_3446_);
v___x_3466_ = lean_apply_7(v_containsRecFn_3444_, v_e_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, lean_box(0));
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3689_; 
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3469_ = v___x_3466_;
v_isShared_3470_ = v_isSharedCheck_3689_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3466_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3689_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
uint8_t v___x_3471_; 
v___x_3471_ = lean_unbox(v_a_3467_);
if (v___x_3471_ == 0)
{
lean_object* v___x_3473_; 
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v_e_3446_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_e_3446_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
else
{
uint8_t v___x_3475_; 
lean_del_object(v___x_3469_);
v___x_3475_ = 0;
switch(lean_obj_tag(v_e_3446_))
{
case 6:
{
lean_object* v_binderName_3476_; lean_object* v_binderType_3477_; lean_object* v_body_3478_; uint8_t v_binderInfo_3479_; lean_object* v___x_3480_; 
v_binderName_3476_ = lean_ctor_get(v_e_3446_, 0);
lean_inc(v_binderName_3476_);
v_binderType_3477_ = lean_ctor_get(v_e_3446_, 1);
lean_inc_ref(v_binderType_3477_);
v_body_3478_ = lean_ctor_get(v_e_3446_, 2);
lean_inc_ref(v_body_3478_);
v_binderInfo_3479_ = lean_ctor_get_uint8(v_e_3446_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3446_);
lean_inc_ref(v_a_3450_);
lean_inc_ref(v_below_3445_);
lean_inc_ref(v_containsRecFn_3444_);
lean_inc_ref(v_recFnNames_3443_);
lean_inc_ref(v_positions_3442_);
lean_inc_ref(v_recArgInfos_3441_);
v___x_3480_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v_below_3445_, v_binderType_3477_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v_a_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; uint8_t v___x_3484_; lean_object* v___x_3485_; 
v_a_3481_ = lean_ctor_get(v___x_3480_, 0);
lean_inc(v_a_3481_);
lean_dec_ref(v___x_3480_);
v___x_3482_ = lean_box(v___x_3475_);
v___f_3483_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3483_, 0, v_body_3478_);
lean_closure_set(v___f_3483_, 1, v_recArgInfos_3441_);
lean_closure_set(v___f_3483_, 2, v_positions_3442_);
lean_closure_set(v___f_3483_, 3, v_recFnNames_3443_);
lean_closure_set(v___f_3483_, 4, v_containsRecFn_3444_);
lean_closure_set(v___f_3483_, 5, v_below_3445_);
lean_closure_set(v___f_3483_, 6, v___x_3482_);
lean_closure_set(v___f_3483_, 7, v_a_3467_);
v___x_3484_ = 0;
v___x_3485_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3476_, v_binderInfo_3479_, v_a_3481_, v___f_3483_, v___x_3484_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec_ref(v_a_3450_);
return v___x_3485_;
}
else
{
lean_dec_ref(v_body_3478_);
lean_dec(v_binderName_3476_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
return v___x_3480_;
}
}
case 7:
{
lean_object* v_binderName_3486_; lean_object* v_binderType_3487_; lean_object* v_body_3488_; uint8_t v_binderInfo_3489_; lean_object* v___x_3490_; 
v_binderName_3486_ = lean_ctor_get(v_e_3446_, 0);
lean_inc(v_binderName_3486_);
v_binderType_3487_ = lean_ctor_get(v_e_3446_, 1);
lean_inc_ref(v_binderType_3487_);
v_body_3488_ = lean_ctor_get(v_e_3446_, 2);
lean_inc_ref(v_body_3488_);
v_binderInfo_3489_ = lean_ctor_get_uint8(v_e_3446_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3446_);
lean_inc_ref(v_a_3450_);
lean_inc_ref(v_below_3445_);
lean_inc_ref(v_containsRecFn_3444_);
lean_inc_ref(v_recFnNames_3443_);
lean_inc_ref(v_positions_3442_);
lean_inc_ref(v_recArgInfos_3441_);
v___x_3490_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v_below_3445_, v_binderType_3487_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3492_; lean_object* v___f_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref(v___x_3490_);
v___x_3492_ = lean_box(v___x_3475_);
v___f_3493_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3493_, 0, v_body_3488_);
lean_closure_set(v___f_3493_, 1, v_recArgInfos_3441_);
lean_closure_set(v___f_3493_, 2, v_positions_3442_);
lean_closure_set(v___f_3493_, 3, v_recFnNames_3443_);
lean_closure_set(v___f_3493_, 4, v_containsRecFn_3444_);
lean_closure_set(v___f_3493_, 5, v_below_3445_);
lean_closure_set(v___f_3493_, 6, v___x_3492_);
lean_closure_set(v___f_3493_, 7, v_a_3467_);
v___x_3494_ = 0;
v___x_3495_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3486_, v_binderInfo_3489_, v_a_3491_, v___f_3493_, v___x_3494_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec_ref(v_a_3450_);
return v___x_3495_;
}
else
{
lean_dec_ref(v_body_3488_);
lean_dec(v_binderName_3486_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
return v___x_3490_;
}
}
case 8:
{
lean_object* v_declName_3496_; lean_object* v_type_3497_; lean_object* v_value_3498_; lean_object* v_body_3499_; uint8_t v_nondep_3500_; lean_object* v___x_3501_; 
lean_dec(v_a_3467_);
v_declName_3496_ = lean_ctor_get(v_e_3446_, 0);
lean_inc(v_declName_3496_);
v_type_3497_ = lean_ctor_get(v_e_3446_, 1);
lean_inc_ref(v_type_3497_);
v_value_3498_ = lean_ctor_get(v_e_3446_, 2);
lean_inc_ref(v_value_3498_);
v_body_3499_ = lean_ctor_get(v_e_3446_, 3);
lean_inc_ref(v_body_3499_);
v_nondep_3500_ = lean_ctor_get_uint8(v_e_3446_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3446_);
lean_inc_ref(v_a_3450_);
lean_inc_ref(v_below_3445_);
lean_inc_ref(v_containsRecFn_3444_);
lean_inc_ref(v_recFnNames_3443_);
lean_inc_ref(v_positions_3442_);
lean_inc_ref(v_recArgInfos_3441_);
v___x_3501_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v_below_3445_, v_type_3497_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref(v___x_3501_);
lean_inc_ref(v_a_3450_);
lean_inc_ref(v_below_3445_);
lean_inc_ref(v_containsRecFn_3444_);
lean_inc_ref(v_recFnNames_3443_);
lean_inc_ref(v_positions_3442_);
lean_inc_ref(v_recArgInfos_3441_);
v___x_3503_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v_below_3445_, v_value_3498_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___f_3505_; uint8_t v___x_3506_; lean_object* v___x_3507_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
v___f_3505_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3505_, 0, v_body_3499_);
lean_closure_set(v___f_3505_, 1, v_recArgInfos_3441_);
lean_closure_set(v___f_3505_, 2, v_positions_3442_);
lean_closure_set(v___f_3505_, 3, v_recFnNames_3443_);
lean_closure_set(v___f_3505_, 4, v_containsRecFn_3444_);
lean_closure_set(v___f_3505_, 5, v_below_3445_);
v___x_3506_ = 0;
v___x_3507_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3496_, v_a_3502_, v_a_3504_, v___f_3505_, v_nondep_3500_, v___x_3506_, v___x_3475_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec_ref(v_a_3450_);
return v___x_3507_;
}
else
{
lean_dec(v_a_3502_);
lean_dec_ref(v_body_3499_);
lean_dec(v_declName_3496_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
return v___x_3503_;
}
}
else
{
lean_dec_ref(v_body_3499_);
lean_dec_ref(v_value_3498_);
lean_dec(v_declName_3496_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
return v___x_3501_;
}
}
case 10:
{
lean_object* v_data_3508_; lean_object* v_expr_3509_; lean_object* v___x_3510_; 
lean_dec(v_a_3467_);
v_data_3508_ = lean_ctor_get(v_e_3446_, 0);
lean_inc(v_data_3508_);
v_expr_3509_ = lean_ctor_get(v_e_3446_, 1);
lean_inc_ref(v_expr_3509_);
v___x_3510_ = l_Lean_getRecAppSyntax_x3f(v_e_3446_);
lean_dec_ref(v_e_3446_);
if (lean_obj_tag(v___x_3510_) == 1)
{
lean_object* v_val_3511_; lean_object* v_fileName_3512_; lean_object* v_fileMap_3513_; lean_object* v_options_3514_; lean_object* v_currRecDepth_3515_; lean_object* v_maxRecDepth_3516_; lean_object* v_ref_3517_; lean_object* v_currNamespace_3518_; lean_object* v_openDecls_3519_; lean_object* v_initHeartbeats_3520_; lean_object* v_maxHeartbeats_3521_; lean_object* v_quotContext_3522_; lean_object* v_currMacroScope_3523_; uint8_t v_diag_3524_; lean_object* v_cancelTk_x3f_3525_; uint8_t v_suppressElabErrors_3526_; lean_object* v_inheritedTraceOptions_3527_; lean_object* v_ref_3528_; lean_object* v___x_3529_; 
lean_dec(v_data_3508_);
v_val_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_val_3511_);
lean_dec_ref(v___x_3510_);
v_fileName_3512_ = lean_ctor_get(v_a_3450_, 0);
lean_inc_ref(v_fileName_3512_);
v_fileMap_3513_ = lean_ctor_get(v_a_3450_, 1);
lean_inc_ref(v_fileMap_3513_);
v_options_3514_ = lean_ctor_get(v_a_3450_, 2);
lean_inc_ref(v_options_3514_);
v_currRecDepth_3515_ = lean_ctor_get(v_a_3450_, 3);
lean_inc(v_currRecDepth_3515_);
v_maxRecDepth_3516_ = lean_ctor_get(v_a_3450_, 4);
lean_inc(v_maxRecDepth_3516_);
v_ref_3517_ = lean_ctor_get(v_a_3450_, 5);
lean_inc(v_ref_3517_);
v_currNamespace_3518_ = lean_ctor_get(v_a_3450_, 6);
lean_inc(v_currNamespace_3518_);
v_openDecls_3519_ = lean_ctor_get(v_a_3450_, 7);
lean_inc(v_openDecls_3519_);
v_initHeartbeats_3520_ = lean_ctor_get(v_a_3450_, 8);
lean_inc(v_initHeartbeats_3520_);
v_maxHeartbeats_3521_ = lean_ctor_get(v_a_3450_, 9);
lean_inc(v_maxHeartbeats_3521_);
v_quotContext_3522_ = lean_ctor_get(v_a_3450_, 10);
lean_inc(v_quotContext_3522_);
v_currMacroScope_3523_ = lean_ctor_get(v_a_3450_, 11);
lean_inc(v_currMacroScope_3523_);
v_diag_3524_ = lean_ctor_get_uint8(v_a_3450_, sizeof(void*)*14);
v_cancelTk_x3f_3525_ = lean_ctor_get(v_a_3450_, 12);
lean_inc(v_cancelTk_x3f_3525_);
v_suppressElabErrors_3526_ = lean_ctor_get_uint8(v_a_3450_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3527_ = lean_ctor_get(v_a_3450_, 13);
lean_inc_ref(v_inheritedTraceOptions_3527_);
lean_dec_ref(v_a_3450_);
v_ref_3528_ = l_Lean_replaceRef(v_val_3511_, v_ref_3517_);
lean_dec(v_ref_3517_);
lean_dec(v_val_3511_);
v___x_3529_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3529_, 0, v_fileName_3512_);
lean_ctor_set(v___x_3529_, 1, v_fileMap_3513_);
lean_ctor_set(v___x_3529_, 2, v_options_3514_);
lean_ctor_set(v___x_3529_, 3, v_currRecDepth_3515_);
lean_ctor_set(v___x_3529_, 4, v_maxRecDepth_3516_);
lean_ctor_set(v___x_3529_, 5, v_ref_3528_);
lean_ctor_set(v___x_3529_, 6, v_currNamespace_3518_);
lean_ctor_set(v___x_3529_, 7, v_openDecls_3519_);
lean_ctor_set(v___x_3529_, 8, v_initHeartbeats_3520_);
lean_ctor_set(v___x_3529_, 9, v_maxHeartbeats_3521_);
lean_ctor_set(v___x_3529_, 10, v_quotContext_3522_);
lean_ctor_set(v___x_3529_, 11, v_currMacroScope_3523_);
lean_ctor_set(v___x_3529_, 12, v_cancelTk_x3f_3525_);
lean_ctor_set(v___x_3529_, 13, v_inheritedTraceOptions_3527_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*14, v_diag_3524_);
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*14 + 1, v_suppressElabErrors_3526_);
v_e_3446_ = v_expr_3509_;
v_a_3450_ = v___x_3529_;
goto _start;
}
else
{
lean_object* v___x_3531_; 
lean_dec(v___x_3510_);
v___x_3531_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v_below_3445_, v_expr_3509_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3540_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3534_ = v___x_3531_;
v_isShared_3535_ = v_isSharedCheck_3540_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3531_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3540_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3536_; lean_object* v___x_3538_; 
v___x_3536_ = l_Lean_mkMData(v_data_3508_, v_a_3532_);
if (v_isShared_3535_ == 0)
{
lean_ctor_set(v___x_3534_, 0, v___x_3536_);
v___x_3538_ = v___x_3534_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
else
{
lean_dec(v_data_3508_);
return v___x_3531_;
}
}
}
case 11:
{
lean_object* v_typeName_3541_; lean_object* v_idx_3542_; lean_object* v_struct_3543_; lean_object* v___x_3544_; 
lean_dec(v_a_3467_);
v_typeName_3541_ = lean_ctor_get(v_e_3446_, 0);
lean_inc(v_typeName_3541_);
v_idx_3542_ = lean_ctor_get(v_e_3446_, 1);
lean_inc(v_idx_3542_);
v_struct_3543_ = lean_ctor_get(v_e_3446_, 2);
lean_inc_ref(v_struct_3543_);
lean_dec_ref(v_e_3446_);
v___x_3544_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v_below_3445_, v_struct_3543_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3553_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3553_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3553_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3551_; 
v___x_3549_ = l_Lean_mkProj(v_typeName_3541_, v_idx_3542_, v_a_3545_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3549_);
v___x_3551_ = v___x_3547_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3549_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
else
{
lean_dec(v_idx_3542_);
lean_dec(v_typeName_3541_);
return v___x_3544_;
}
}
case 5:
{
uint8_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3554_ = lean_unbox(v_a_3467_);
lean_inc_ref(v_e_3446_);
v___x_3555_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3446_, v___x_3554_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v___x_3555_);
if (lean_obj_tag(v_a_3556_) == 0)
{
lean_dec(v_a_3467_);
v_e_3454_ = v_e_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
v___y_3458_ = v_a_3450_;
v___y_3459_ = v_a_3451_;
goto v___jp_3453_;
}
else
{
lean_object* v_val_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v_val_3557_ = lean_ctor_get(v_a_3556_, 0);
lean_inc(v_val_3557_);
lean_dec_ref(v_a_3556_);
v___x_3558_ = lean_unsigned_to_nat(0u);
v___x_3559_ = lean_array_get_size(v_recArgInfos_3441_);
v___x_3560_ = lean_nat_dec_lt(v___x_3558_, v___x_3559_);
if (v___x_3560_ == 0)
{
lean_dec(v_val_3557_);
lean_dec(v_a_3467_);
v_e_3454_ = v_e_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
v___y_3458_ = v_a_3450_;
v___y_3459_ = v_a_3451_;
goto v___jp_3453_;
}
else
{
if (v___x_3560_ == 0)
{
lean_dec(v_val_3557_);
lean_dec(v_a_3467_);
v_e_3454_ = v_e_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
v___y_3458_ = v_a_3450_;
v___y_3459_ = v_a_3451_;
goto v___jp_3453_;
}
else
{
size_t v___x_3561_; size_t v___x_3562_; uint8_t v___x_3563_; 
v___x_3561_ = ((size_t)0ULL);
v___x_3562_ = lean_usize_of_nat(v___x_3559_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3446_, v_recArgInfos_3441_, v___x_3561_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_dec(v_val_3557_);
lean_dec(v_a_3467_);
v_e_3454_ = v_e_3446_;
v___y_3455_ = v_a_3447_;
v___y_3456_ = v_a_3448_;
v___y_3457_ = v_a_3449_;
v___y_3458_ = v_a_3450_;
v___y_3459_ = v_a_3451_;
goto v___jp_3453_;
}
else
{
lean_object* v_inheritedTraceOptions_3564_; lean_object* v___x_3565_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___x_3635_; 
v_inheritedTraceOptions_3564_ = lean_ctor_get(v_a_3450_, 13);
v___x_3565_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3635_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3565_, v_inheritedTraceOptions_3564_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; uint8_t v___x_3637_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_a_3636_);
lean_dec_ref(v___x_3635_);
v___x_3637_ = lean_unbox(v_a_3636_);
lean_dec(v_a_3636_);
if (v___x_3637_ == 0)
{
v___y_3567_ = v_a_3447_;
v___y_3568_ = v_a_3448_;
v___y_3569_ = v_a_3449_;
v___y_3570_ = v_a_3450_;
v___y_3571_ = v_a_3451_;
goto v___jp_3566_;
}
else
{
lean_object* v___x_3638_; 
lean_inc(v_a_3451_);
lean_inc_ref(v_a_3450_);
lean_inc(v_a_3449_);
lean_inc_ref(v_a_3448_);
lean_inc_ref(v_below_3445_);
v___x_3638_ = lean_infer_type(v_below_3445_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
lean_inc(v_a_3639_);
lean_dec_ref(v___x_3638_);
v___x_3640_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3445_);
v___x_3641_ = l_Lean_MessageData_ofExpr(v_below_3445_);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3640_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = l_Lean_MessageData_ofExpr(v_a_3639_);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3565_, v___x_3646_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_dec_ref(v___x_3647_);
v___y_3567_ = v_a_3447_;
v___y_3568_ = v_a_3448_;
v___y_3569_ = v_a_3449_;
v___y_3570_ = v_a_3450_;
v___y_3571_ = v_a_3451_;
goto v___jp_3566_;
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3446_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3653_; 
if (v_isShared_3651_ == 0)
{
v___x_3653_ = v___x_3650_;
goto v_reusejp_3652_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3648_);
v___x_3653_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3652_;
}
v_reusejp_3652_:
{
return v___x_3653_;
}
}
}
}
else
{
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3446_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
return v___x_3638_;
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3446_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
v_a_3656_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3635_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3635_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
v___jp_3566_:
{
lean_object* v___x_3572_; 
lean_inc_ref(v_below_3445_);
v___x_3572_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3557_, v_below_3445_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref(v___x_3572_);
if (lean_obj_tag(v_a_3573_) == 1)
{
lean_object* v_val_3574_; lean_object* v_toMatcherInfo_3575_; lean_object* v_matcherName_3576_; lean_object* v_matcherLevels_3577_; lean_object* v_params_3578_; lean_object* v_motive_3579_; lean_object* v_discrs_3580_; lean_object* v_alts_3581_; lean_object* v_remaining_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; lean_object* v___x_3586_; 
lean_dec_ref(v_below_3445_);
v_val_3574_ = lean_ctor_get(v_a_3573_, 0);
lean_inc(v_val_3574_);
lean_dec_ref(v_a_3573_);
v_toMatcherInfo_3575_ = lean_ctor_get(v_val_3574_, 0);
lean_inc_ref(v_toMatcherInfo_3575_);
v_matcherName_3576_ = lean_ctor_get(v_val_3574_, 1);
lean_inc(v_matcherName_3576_);
v_matcherLevels_3577_ = lean_ctor_get(v_val_3574_, 2);
lean_inc_ref(v_matcherLevels_3577_);
v_params_3578_ = lean_ctor_get(v_val_3574_, 3);
lean_inc_ref(v_params_3578_);
v_motive_3579_ = lean_ctor_get(v_val_3574_, 4);
lean_inc_ref(v_motive_3579_);
v_discrs_3580_ = lean_ctor_get(v_val_3574_, 5);
lean_inc_ref(v_discrs_3580_);
v_alts_3581_ = lean_ctor_get(v_val_3574_, 6);
lean_inc_ref(v_alts_3581_);
v_remaining_3582_ = lean_ctor_get(v_val_3574_, 7);
lean_inc_ref(v_remaining_3582_);
v___x_3583_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3574_);
v___x_3584_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3585_ = lean_unbox(v_a_3467_);
lean_dec(v_a_3467_);
v___x_3586_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v___x_3585_, v_e_3446_, v_alts_3581_, v___x_3583_, v___x_3558_, v___x_3584_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___x_3583_);
lean_dec_ref(v_alts_3581_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3596_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3596_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3591_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3591_, 0, v_toMatcherInfo_3575_);
lean_ctor_set(v___x_3591_, 1, v_matcherName_3576_);
lean_ctor_set(v___x_3591_, 2, v_matcherLevels_3577_);
lean_ctor_set(v___x_3591_, 3, v_params_3578_);
lean_ctor_set(v___x_3591_, 4, v_motive_3579_);
lean_ctor_set(v___x_3591_, 5, v_discrs_3580_);
lean_ctor_set(v___x_3591_, 6, v_a_3587_);
lean_ctor_set(v___x_3591_, 7, v_remaining_3582_);
v___x_3592_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3591_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 0, v___x_3592_);
v___x_3594_ = v___x_3589_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v_remaining_3582_);
lean_dec_ref(v_discrs_3580_);
lean_dec_ref(v_motive_3579_);
lean_dec_ref(v_params_3578_);
lean_dec_ref(v_matcherLevels_3577_);
lean_dec(v_matcherName_3576_);
lean_dec_ref(v_toMatcherInfo_3575_);
v_a_3597_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3586_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3586_);
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
else
{
lean_object* v_inheritedTraceOptions_3605_; lean_object* v___x_3606_; 
lean_dec(v_a_3573_);
lean_dec(v_a_3467_);
v_inheritedTraceOptions_3605_ = lean_ctor_get(v___y_3570_, 13);
v___x_3606_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3565_, v_inheritedTraceOptions_3605_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; uint8_t v___x_3608_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref(v___x_3606_);
v___x_3608_ = lean_unbox(v_a_3607_);
lean_dec(v_a_3607_);
if (v___x_3608_ == 0)
{
v_e_3454_ = v_e_3446_;
v___y_3455_ = v___y_3567_;
v___y_3456_ = v___y_3568_;
v___y_3457_ = v___y_3569_;
v___y_3458_ = v___y_3570_;
v___y_3459_ = v___y_3571_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3610_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3565_, v___x_3609_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_dec_ref(v___x_3610_);
v_e_3454_ = v_e_3446_;
v___y_3455_ = v___y_3567_;
v___y_3456_ = v___y_3568_;
v___y_3457_ = v___y_3569_;
v___y_3458_ = v___y_3570_;
v___y_3459_ = v___y_3571_;
goto v___jp_3453_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v___y_3570_);
lean_dec_ref(v_e_3446_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
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
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref(v___y_3570_);
lean_dec_ref(v_e_3446_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
v_a_3619_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3606_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3606_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v___y_3570_);
lean_dec_ref(v_e_3446_);
lean_dec(v_a_3467_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
v_a_3627_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3572_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3572_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
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
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec_ref(v_e_3446_);
lean_dec(v_a_3467_);
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
v_a_3664_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3555_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3555_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
default: 
{
lean_object* v___x_3672_; 
lean_dec(v_a_3467_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
lean_inc_ref(v_e_3446_);
v___x_3672_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3443_, v_e_3446_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec_ref(v_a_3450_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3679_ == 0)
{
lean_object* v_unused_3680_; 
v_unused_3680_ = lean_ctor_get(v___x_3672_, 0);
lean_dec(v_unused_3680_);
v___x_3674_ = v___x_3672_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v___x_3672_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v_e_3446_);
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_e_3446_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v_e_3446_);
v_a_3681_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3672_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3672_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
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
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec_ref(v_a_3450_);
lean_dec_ref(v_e_3446_);
lean_dec_ref(v_below_3445_);
lean_dec_ref(v_containsRecFn_3444_);
lean_dec_ref(v_recFnNames_3443_);
lean_dec_ref(v_positions_3442_);
lean_dec_ref(v_recArgInfos_3441_);
v_a_3690_ = lean_ctor_get(v___x_3466_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3466_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3466_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3466_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
v___jp_3453_:
{
lean_object* v_dummy_3460_; lean_object* v_nargs_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v_dummy_3460_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3461_ = l_Lean_Expr_getAppNumArgs(v_e_3454_);
lean_inc(v_nargs_3461_);
v___x_3462_ = lean_mk_array(v_nargs_3461_, v_dummy_3460_);
v___x_3463_ = lean_unsigned_to_nat(1u);
v___x_3464_ = lean_nat_sub(v_nargs_3461_, v___x_3463_);
lean_dec(v_nargs_3461_);
lean_inc_ref(v_e_3454_);
v___x_3465_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3441_, v_positions_3442_, v_recFnNames_3443_, v_containsRecFn_3444_, v_below_3445_, v_e_3454_, v_e_3454_, v___x_3462_, v___x_3464_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec_ref(v___y_3458_);
return v___x_3465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3698_, lean_object* v_recArgInfos_3699_, lean_object* v_positions_3700_, lean_object* v_recFnNames_3701_, lean_object* v_containsRecFn_3702_, lean_object* v_below_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = lean_expr_instantiate1(v_body_3698_, v_x_3704_);
lean_inc_ref(v___y_3708_);
v___x_3712_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3699_, v_positions_3700_, v_recFnNames_3701_, v_containsRecFn_3702_, v_below_3703_, v___x_3711_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3713_, lean_object* v_positions_3714_, lean_object* v_recFnNames_3715_, lean_object* v_containsRecFn_3716_, lean_object* v_below_3717_, lean_object* v_sz_3718_, lean_object* v_i_3719_, lean_object* v_bs_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
size_t v_sz_boxed_3727_; size_t v_i_boxed_3728_; lean_object* v_res_3729_; 
v_sz_boxed_3727_ = lean_unbox_usize(v_sz_3718_);
lean_dec(v_sz_3718_);
v_i_boxed_3728_ = lean_unbox_usize(v_i_3719_);
lean_dec(v_i_3719_);
v_res_3729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3713_, v_positions_3714_, v_recFnNames_3715_, v_containsRecFn_3716_, v_below_3717_, v_sz_boxed_3727_, v_i_boxed_3728_, v_bs_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3730_, lean_object* v_positions_3731_, lean_object* v_recFnNames_3732_, lean_object* v_containsRecFn_3733_, lean_object* v_a_3734_, lean_object* v_e_3735_, lean_object* v_as_3736_, lean_object* v_bs_3737_, lean_object* v_i_3738_, lean_object* v_cs_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
uint8_t v_a_32883__boxed_3746_; lean_object* v_res_3747_; 
v_a_32883__boxed_3746_ = lean_unbox(v_a_3734_);
v_res_3747_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3730_, v_positions_3731_, v_recFnNames_3732_, v_containsRecFn_3733_, v_a_32883__boxed_3746_, v_e_3735_, v_as_3736_, v_bs_3737_, v_i_3738_, v_cs_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v_bs_3737_);
lean_dec_ref(v_as_3736_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3748_, lean_object* v_positions_3749_, lean_object* v_recFnNames_3750_, lean_object* v_containsRecFn_3751_, lean_object* v_below_3752_, lean_object* v_e_3753_, lean_object* v_x_3754_, lean_object* v_x_3755_, lean_object* v_x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3748_, v_positions_3749_, v_recFnNames_3750_, v_containsRecFn_3751_, v_below_3752_, v_e_3753_, v_x_3754_, v_x_3755_, v_x_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3764_, lean_object* v_positions_3765_, lean_object* v_recFnNames_3766_, lean_object* v_containsRecFn_3767_, lean_object* v_below_3768_, lean_object* v_e_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3764_, v_positions_3765_, v_recFnNames_3766_, v_containsRecFn_3767_, v_below_3768_, v_e_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_);
lean_dec(v_a_3774_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3777_, lean_object* v_msg_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3778_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3786_, lean_object* v_msg_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3786_, v_msg_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3795_, lean_object* v_name_3796_, lean_object* v_type_3797_, lean_object* v_val_3798_, lean_object* v_k_3799_, uint8_t v_nondep_3800_, uint8_t v_kind_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3796_, v_type_3797_, v_val_3798_, v_k_3799_, v_nondep_3800_, v_kind_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3809_, lean_object* v_name_3810_, lean_object* v_type_3811_, lean_object* v_val_3812_, lean_object* v_k_3813_, lean_object* v_nondep_3814_, lean_object* v_kind_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v_nondep_boxed_3822_; uint8_t v_kind_boxed_3823_; lean_object* v_res_3824_; 
v_nondep_boxed_3822_ = lean_unbox(v_nondep_3814_);
v_kind_boxed_3823_ = lean_unbox(v_kind_3815_);
v_res_3824_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3809_, v_name_3810_, v_type_3811_, v_val_3812_, v_k_3813_, v_nondep_boxed_3822_, v_kind_boxed_3823_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3825_, v___y_3830_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3841_, lean_object* v_msg_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3841_, v_msg_3842_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3850_, lean_object* v_msg_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3850_, v_msg_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
return v_res_3858_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3859_, lean_object* v_constName_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3868_, lean_object* v_constName_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3868_, v_constName_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3877_, lean_object* v_ref_3878_, lean_object* v_constName_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3878_, v_constName_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3887_, lean_object* v_ref_3888_, lean_object* v_constName_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3887_, v_ref_3888_, v_constName_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec(v_ref_3888_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3897_, lean_object* v_ref_3898_, lean_object* v_msg_3899_, lean_object* v_declHint_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3898_, v_msg_3899_, v_declHint_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3908_, lean_object* v_ref_3909_, lean_object* v_msg_3910_, lean_object* v_declHint_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
lean_object* v_res_3918_; 
v_res_3918_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3908_, v_ref_3909_, v_msg_3910_, v_declHint_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec(v_ref_3909_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3919_, lean_object* v_declHint_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3919_, v_declHint_3920_, v___y_3925_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3928_, lean_object* v_declHint_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3928_, v_declHint_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3937_, lean_object* v_ref_3938_, lean_object* v_msg_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
lean_object* v___x_3946_; 
v___x_3946_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3938_, v_msg_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v___x_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3947_, lean_object* v_ref_3948_, lean_object* v_msg_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
lean_object* v_res_3956_; 
v_res_3956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3947_, v_ref_3948_, v_msg_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
lean_dec(v___y_3954_);
lean_dec_ref(v___y_3953_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec(v_ref_3948_);
return v_res_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3957_, lean_object* v_e_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v_fst_3967_; lean_object* v_snd_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3965_ = lean_st_ref_take(v___y_3959_);
v___x_3966_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3957_, v_e_3958_, v___x_3965_);
v_fst_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_fst_3967_);
v_snd_3968_ = lean_ctor_get(v___x_3966_, 1);
lean_inc(v_snd_3968_);
lean_dec_ref(v___x_3966_);
v___x_3969_ = lean_st_ref_set(v___y_3959_, v_snd_3968_);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v_fst_3967_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3971_, lean_object* v_e_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3971_, v_e_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v_recFnNames_3971_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3980_, size_t v_i_3981_, lean_object* v_bs_3982_){
_start:
{
uint8_t v___x_3983_; 
v___x_3983_ = lean_usize_dec_lt(v_i_3981_, v_sz_3980_);
if (v___x_3983_ == 0)
{
return v_bs_3982_;
}
else
{
lean_object* v_v_3984_; lean_object* v_fnName_3985_; lean_object* v___x_3986_; lean_object* v_bs_x27_3987_; size_t v___x_3988_; size_t v___x_3989_; lean_object* v___x_3990_; 
v_v_3984_ = lean_array_uget_borrowed(v_bs_3982_, v_i_3981_);
v_fnName_3985_ = lean_ctor_get(v_v_3984_, 0);
lean_inc(v_fnName_3985_);
v___x_3986_ = lean_unsigned_to_nat(0u);
v_bs_x27_3987_ = lean_array_uset(v_bs_3982_, v_i_3981_, v___x_3986_);
v___x_3988_ = ((size_t)1ULL);
v___x_3989_ = lean_usize_add(v_i_3981_, v___x_3988_);
v___x_3990_ = lean_array_uset(v_bs_x27_3987_, v_i_3981_, v_fnName_3985_);
v_i_3981_ = v___x_3989_;
v_bs_3982_ = v___x_3990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3992_, lean_object* v_i_3993_, lean_object* v_bs_3994_){
_start:
{
size_t v_sz_boxed_3995_; size_t v_i_boxed_3996_; lean_object* v_res_3997_; 
v_sz_boxed_3995_ = lean_unbox_usize(v_sz_3992_);
lean_dec(v_sz_3992_);
v_i_boxed_3996_ = lean_unbox_usize(v_i_3993_);
lean_dec(v_i_3993_);
v_res_3997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3995_, v_i_boxed_3996_, v_bs_3994_);
return v_res_3997_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_unsigned_to_nat(16u);
v___x_4000_ = lean_mk_array(v___x_3999_, v___x_3998_);
return v___x_4000_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_4002_ = lean_unsigned_to_nat(0u);
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v___x_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_4004_, lean_object* v_positions_4005_, lean_object* v_below_4006_, lean_object* v_e_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; size_t v_sz_4015_; size_t v___x_4016_; lean_object* v_recFnNames_4017_; lean_object* v_containsRecFn_4018_; lean_object* v___x_4019_; 
v___x_4013_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_4014_ = lean_st_mk_ref(v___x_4013_);
v_sz_4015_ = lean_array_size(v_recArgInfos_4004_);
v___x_4016_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_4004_);
v_recFnNames_4017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_4015_, v___x_4016_, v_recArgInfos_4004_);
lean_inc_ref(v_recFnNames_4017_);
v_containsRecFn_4018_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_4018_, 0, v_recFnNames_4017_);
lean_inc_ref(v_a_4010_);
v___x_4019_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_4004_, v_positions_4005_, v_recFnNames_4017_, v_containsRecFn_4018_, v_below_4006_, v_e_4007_, v___x_4014_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4028_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4022_ = v___x_4019_;
v_isShared_4023_ = v_isSharedCheck_4028_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4019_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4028_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4024_; lean_object* v___x_4026_; 
v___x_4024_ = lean_st_ref_get(v___x_4014_);
lean_dec(v___x_4014_);
lean_dec(v___x_4024_);
if (v_isShared_4023_ == 0)
{
v___x_4026_ = v___x_4022_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4020_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
else
{
lean_dec(v___x_4014_);
return v___x_4019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_4029_, lean_object* v_positions_4030_, lean_object* v_below_4031_, lean_object* v_e_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_){
_start:
{
lean_object* v_res_4038_; 
v_res_4038_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4029_, v_positions_4030_, v_below_4031_, v_e_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4039_, lean_object* v_k_4040_, uint8_t v_cleanupAnnotations_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v___f_4047_; uint8_t v___x_4048_; uint8_t v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___f_4047_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4047_, 0, v_k_4040_);
v___x_4048_ = 1;
v___x_4049_ = 0;
v___x_4050_ = lean_box(0);
v___x_4051_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4039_, v___x_4048_, v___x_4049_, v___x_4048_, v___x_4049_, v___x_4050_, v___f_4047_, v_cleanupAnnotations_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4051_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4051_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4051_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4051_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4068_, lean_object* v_k_4069_, lean_object* v_cleanupAnnotations_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4076_; lean_object* v_res_4077_; 
v_cleanupAnnotations_boxed_4076_ = lean_unbox(v_cleanupAnnotations_4070_);
v_res_4077_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4068_, v_k_4069_, v_cleanupAnnotations_boxed_4076_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4078_, lean_object* v_e_4079_, lean_object* v_k_4080_, uint8_t v_cleanupAnnotations_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4079_, v_k_4080_, v_cleanupAnnotations_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4088_, lean_object* v_e_4089_, lean_object* v_k_4090_, lean_object* v_cleanupAnnotations_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4097_; lean_object* v_res_4098_; 
v_cleanupAnnotations_boxed_4097_ = lean_unbox(v_cleanupAnnotations_4091_);
v_res_4098_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4088_, v_e_4089_, v_k_4090_, v_cleanupAnnotations_boxed_4097_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4099_, lean_object* v_recArgInfo_4100_, lean_object* v_xs_4101_, lean_object* v___value_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_Meta_instantiateForall(v_type_4099_, v_xs_4101_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4110_; lean_object* v_fst_4111_; lean_object* v_snd_4112_; uint8_t v___x_4113_; uint8_t v___x_4114_; uint8_t v___x_4115_; lean_object* v___x_4116_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc(v_a_4109_);
lean_dec_ref(v___x_4108_);
v___x_4110_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4100_, v_xs_4101_);
v_fst_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_fst_4111_);
v_snd_4112_ = lean_ctor_get(v___x_4110_, 1);
lean_inc(v_snd_4112_);
lean_dec_ref(v___x_4110_);
v___x_4113_ = 0;
v___x_4114_ = 1;
v___x_4115_ = 1;
v___x_4116_ = l_Lean_Meta_mkForallFVars(v_snd_4112_, v_a_4109_, v___x_4113_, v___x_4114_, v___x_4114_, v___x_4115_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v_snd_4112_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = l_Lean_Meta_mkLambdaFVars(v_fst_4111_, v_a_4117_, v___x_4113_, v___x_4114_, v___x_4113_, v___x_4114_, v___x_4115_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
lean_dec(v_fst_4111_);
return v___x_4118_;
}
else
{
lean_dec(v_fst_4111_);
return v___x_4116_;
}
}
else
{
lean_dec_ref(v_xs_4101_);
lean_dec_ref(v_recArgInfo_4100_);
return v___x_4108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4119_, lean_object* v_recArgInfo_4120_, lean_object* v_xs_4121_, lean_object* v___value_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4119_, v_recArgInfo_4120_, v_xs_4121_, v___value_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec_ref(v___value_4122_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4129_, lean_object* v_value_4130_, lean_object* v_type_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___f_4137_; uint8_t v___x_4138_; lean_object* v___x_4139_; 
v___f_4137_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4137_, 0, v_type_4131_);
lean_closure_set(v___f_4137_, 1, v_recArgInfo_4129_);
v___x_4138_ = 0;
v___x_4139_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4130_, v___f_4137_, v___x_4138_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4140_, lean_object* v_value_4141_, lean_object* v_type_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4140_, v_value_4141_, v_type_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(lean_object* v_type_4149_, lean_object* v_maxFVars_x3f_4150_, lean_object* v_k_4151_, uint8_t v_cleanupAnnotations_4152_, uint8_t v_whnfType_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v___f_4159_; lean_object* v___x_4160_; 
v___f_4159_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4159_, 0, v_k_4151_);
v___x_4160_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4149_, v_maxFVars_x3f_4150_, v___f_4159_, v_cleanupAnnotations_4152_, v_whnfType_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4160_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
v_a_4169_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4160_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4160_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg___boxed(lean_object* v_type_4177_, lean_object* v_maxFVars_x3f_4178_, lean_object* v_k_4179_, lean_object* v_cleanupAnnotations_4180_, lean_object* v_whnfType_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4187_; uint8_t v_whnfType_boxed_4188_; lean_object* v_res_4189_; 
v_cleanupAnnotations_boxed_4187_ = lean_unbox(v_cleanupAnnotations_4180_);
v_whnfType_boxed_4188_ = lean_unbox(v_whnfType_4181_);
v_res_4189_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4177_, v_maxFVars_x3f_4178_, v_k_4179_, v_cleanupAnnotations_boxed_4187_, v_whnfType_boxed_4188_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
lean_dec_ref(v___y_4182_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(lean_object* v_00_u03b1_4190_, lean_object* v_type_4191_, lean_object* v_maxFVars_x3f_4192_, lean_object* v_k_4193_, uint8_t v_cleanupAnnotations_4194_, uint8_t v_whnfType_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_type_4191_, v_maxFVars_x3f_4192_, v_k_4193_, v_cleanupAnnotations_4194_, v_whnfType_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___boxed(lean_object* v_00_u03b1_4202_, lean_object* v_type_4203_, lean_object* v_maxFVars_x3f_4204_, lean_object* v_k_4205_, lean_object* v_cleanupAnnotations_4206_, lean_object* v_whnfType_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4213_; uint8_t v_whnfType_boxed_4214_; lean_object* v_res_4215_; 
v_cleanupAnnotations_boxed_4213_ = lean_unbox(v_cleanupAnnotations_4206_);
v_whnfType_boxed_4214_ = lean_unbox(v_whnfType_4207_);
v_res_4215_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0(v_00_u03b1_4202_, v_type_4203_, v_maxFVars_x3f_4204_, v_k_4205_, v_cleanupAnnotations_boxed_4213_, v_whnfType_boxed_4214_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v___x_4216_, lean_object* v_recArgInfos_4217_, lean_object* v_positions_4218_, lean_object* v_value_4219_, lean_object* v_fst_4220_, lean_object* v_snd_4221_, lean_object* v_below_4222_, lean_object* v_x_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4229_ = lean_unsigned_to_nat(0u);
v___x_4230_ = lean_array_get_borrowed(v___x_4216_, v_below_4222_, v___x_4229_);
lean_inc(v___x_4230_);
v___x_4231_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4217_, v_positions_4218_, v___x_4230_, v_value_4219_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; uint8_t v___x_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref(v___x_4231_);
v___x_4233_ = lean_unsigned_to_nat(1u);
v___x_4234_ = lean_mk_empty_array_with_capacity(v___x_4233_);
lean_inc(v___x_4230_);
v___x_4235_ = lean_array_push(v___x_4234_, v___x_4230_);
v___x_4236_ = l_Array_append___redArg(v_fst_4220_, v___x_4235_);
lean_dec_ref(v___x_4235_);
v___x_4237_ = l_Array_append___redArg(v___x_4236_, v_snd_4221_);
v___x_4238_ = 0;
v___x_4239_ = 1;
v___x_4240_ = 1;
v___x_4241_ = l_Lean_Meta_mkLambdaFVars(v___x_4237_, v_a_4232_, v___x_4238_, v___x_4239_, v___x_4238_, v___x_4239_, v___x_4240_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec_ref(v___x_4237_);
return v___x_4241_;
}
else
{
lean_dec_ref(v_fst_4220_);
return v___x_4231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v___x_4242_, lean_object* v_recArgInfos_4243_, lean_object* v_positions_4244_, lean_object* v_value_4245_, lean_object* v_fst_4246_, lean_object* v_snd_4247_, lean_object* v_below_4248_, lean_object* v_x_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v___x_4242_, v_recArgInfos_4243_, v_positions_4244_, v_value_4245_, v_fst_4246_, v_snd_4247_, v_below_4248_, v_x_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec_ref(v_x_4249_);
lean_dec_ref(v_below_4248_);
lean_dec_ref(v_snd_4247_);
lean_dec_ref(v___x_4242_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4258_, lean_object* v_FType_4259_, lean_object* v___x_4260_, lean_object* v_recArgInfos_4261_, lean_object* v_positions_4262_, lean_object* v_xs_4263_, lean_object* v_value_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v___x_4270_; lean_object* v_fst_4271_; lean_object* v_snd_4272_; lean_object* v___x_4273_; 
v___x_4270_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4258_, v_xs_4263_);
v_fst_4271_ = lean_ctor_get(v___x_4270_, 0);
lean_inc(v_fst_4271_);
v_snd_4272_ = lean_ctor_get(v___x_4270_, 1);
lean_inc(v_snd_4272_);
lean_dec_ref(v___x_4270_);
v___x_4273_ = l_Lean_Meta_instantiateForall(v_FType_4259_, v_fst_4271_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___f_4275_; lean_object* v___x_4276_; uint8_t v___x_4277_; lean_object* v___x_4278_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_a_4274_);
lean_dec_ref(v___x_4273_);
v___f_4275_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 13, 6);
lean_closure_set(v___f_4275_, 0, v___x_4260_);
lean_closure_set(v___f_4275_, 1, v_recArgInfos_4261_);
lean_closure_set(v___f_4275_, 2, v_positions_4262_);
lean_closure_set(v___f_4275_, 3, v_value_4264_);
lean_closure_set(v___f_4275_, 4, v_fst_4271_);
lean_closure_set(v___f_4275_, 5, v_snd_4272_);
v___x_4276_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4277_ = 0;
v___x_4278_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4274_, v___x_4276_, v___f_4275_, v___x_4277_, v___x_4277_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
return v___x_4278_;
}
else
{
lean_dec(v_snd_4272_);
lean_dec(v_fst_4271_);
lean_dec_ref(v_value_4264_);
lean_dec_ref(v_positions_4262_);
lean_dec_ref(v_recArgInfos_4261_);
lean_dec_ref(v___x_4260_);
return v___x_4273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4279_, lean_object* v_FType_4280_, lean_object* v___x_4281_, lean_object* v_recArgInfos_4282_, lean_object* v_positions_4283_, lean_object* v_xs_4284_, lean_object* v_value_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4279_, v_FType_4280_, v___x_4281_, v_recArgInfos_4282_, v_positions_4283_, v_xs_4284_, v_value_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4292_, lean_object* v_positions_4293_, lean_object* v_recArgInfo_4294_, lean_object* v_value_4295_, lean_object* v_FType_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v___x_4302_; lean_object* v___f_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; 
v___x_4302_ = l_Lean_instInhabitedExpr;
v___f_4303_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4303_, 0, v_recArgInfo_4294_);
lean_closure_set(v___f_4303_, 1, v_FType_4296_);
lean_closure_set(v___f_4303_, 2, v___x_4302_);
lean_closure_set(v___f_4303_, 3, v_recArgInfos_4292_);
lean_closure_set(v___f_4303_, 4, v_positions_4293_);
v___x_4304_ = 0;
v___x_4305_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4295_, v___f_4303_, v___x_4304_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4306_, lean_object* v_positions_4307_, lean_object* v_recArgInfo_4308_, lean_object* v_value_4309_, lean_object* v_FType_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4306_, v_positions_4307_, v_recArgInfo_4308_, v_value_4309_, v_FType_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4317_, lean_object* v_params_4318_, uint8_t v_isIndPred_4319_, lean_object* v_brecOnUniv_4320_, lean_object* v_levels_4321_, lean_object* v_idx_4322_){
_start:
{
lean_object* v_n_4323_; lean_object* v___y_4325_; 
v_n_4323_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4317_, v_idx_4322_);
if (v_isIndPred_4319_ == 0)
{
lean_object* v___x_4328_; 
v___x_4328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4328_, 0, v_brecOnUniv_4320_);
lean_ctor_set(v___x_4328_, 1, v_levels_4321_);
v___y_4325_ = v___x_4328_;
goto v___jp_4324_;
}
else
{
lean_dec(v_brecOnUniv_4320_);
v___y_4325_ = v_levels_4321_;
goto v___jp_4324_;
}
v___jp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = l_Lean_Expr_const___override(v_n_4323_, v___y_4325_);
v___x_4327_ = l_Lean_mkAppN(v___x_4326_, v_params_4318_);
return v___x_4327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4329_, lean_object* v_params_4330_, lean_object* v_isIndPred_4331_, lean_object* v_brecOnUniv_4332_, lean_object* v_levels_4333_, lean_object* v_idx_4334_){
_start:
{
uint8_t v_isIndPred_boxed_4335_; lean_object* v_res_4336_; 
v_isIndPred_boxed_4335_ = lean_unbox(v_isIndPred_4331_);
v_res_4336_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4329_, v_params_4330_, v_isIndPred_boxed_4335_, v_brecOnUniv_4332_, v_levels_4333_, v_idx_4334_);
lean_dec(v_idx_4334_);
lean_dec_ref(v_params_4330_);
lean_dec_ref(v_toIndGroupInfo_4329_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4337_, lean_object* v_a_4338_, lean_object* v_n_4339_){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4340_ = lean_apply_1(v_brecOnCons_4337_, v_n_4339_);
v___x_4341_ = l_Lean_mkAppN(v___x_4340_, v_a_4338_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4342_, lean_object* v_a_4343_, lean_object* v_n_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4342_, v_a_4343_, v_n_4344_);
lean_dec_ref(v_a_4343_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4346_, lean_object* v_type_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v___x_4353_; 
v___x_4353_ = l_Lean_Meta_getLevel(v_type_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4354_, lean_object* v_type_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4354_, v_type_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
lean_dec_ref(v_x_4354_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4362_, size_t v_sz_4363_, size_t v_i_4364_, lean_object* v_bs_4365_){
_start:
{
uint8_t v___x_4366_; 
v___x_4366_ = lean_usize_dec_lt(v_i_4364_, v_sz_4363_);
if (v___x_4366_ == 0)
{
return v_bs_4365_;
}
else
{
lean_object* v___x_4367_; lean_object* v_v_4368_; lean_object* v___x_4369_; lean_object* v_bs_x27_4370_; lean_object* v___x_4371_; size_t v___x_4372_; size_t v___x_4373_; lean_object* v___x_4374_; 
v___x_4367_ = l_Lean_instInhabitedExpr;
v_v_4368_ = lean_array_uget(v_bs_4365_, v_i_4364_);
v___x_4369_ = lean_unsigned_to_nat(0u);
v_bs_x27_4370_ = lean_array_uset(v_bs_4365_, v_i_4364_, v___x_4369_);
v___x_4371_ = lean_array_get_borrowed(v___x_4367_, v_xs_4362_, v_v_4368_);
lean_dec(v_v_4368_);
v___x_4372_ = ((size_t)1ULL);
v___x_4373_ = lean_usize_add(v_i_4364_, v___x_4372_);
lean_inc(v___x_4371_);
v___x_4374_ = lean_array_uset(v_bs_x27_4370_, v_i_4364_, v___x_4371_);
v_i_4364_ = v___x_4373_;
v_bs_4365_ = v___x_4374_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4376_, lean_object* v_sz_4377_, lean_object* v_i_4378_, lean_object* v_bs_4379_){
_start:
{
size_t v_sz_boxed_4380_; size_t v_i_boxed_4381_; lean_object* v_res_4382_; 
v_sz_boxed_4380_ = lean_unbox_usize(v_sz_4377_);
lean_dec(v_sz_4377_);
v_i_boxed_4381_ = lean_unbox_usize(v_i_4378_);
lean_dec(v_i_4378_);
v_res_4382_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4376_, v_sz_boxed_4380_, v_i_boxed_4381_, v_bs_4379_);
lean_dec_ref(v_xs_4376_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4383_, lean_object* v_f_4384_, lean_object* v_as_4385_, lean_object* v_bs_4386_, lean_object* v_i_4387_, lean_object* v_cs_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; uint8_t v___x_4395_; 
v___x_4394_ = lean_array_get_size(v_as_4385_);
v___x_4395_ = lean_nat_dec_lt(v_i_4387_, v___x_4394_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4396_; 
lean_dec(v_i_4387_);
lean_dec_ref(v_f_4384_);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v_cs_4388_);
return v___x_4396_;
}
else
{
lean_object* v___x_4397_; uint8_t v___x_4398_; 
v___x_4397_ = lean_array_get_size(v_bs_4386_);
v___x_4398_ = lean_nat_dec_lt(v_i_4387_, v___x_4397_);
if (v___x_4398_ == 0)
{
lean_object* v___x_4399_; 
lean_dec(v_i_4387_);
lean_dec_ref(v_f_4384_);
v___x_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4399_, 0, v_cs_4388_);
return v___x_4399_;
}
else
{
lean_object* v_a_4400_; lean_object* v_b_4401_; size_t v_sz_4402_; size_t v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_a_4400_ = lean_array_fget_borrowed(v_as_4385_, v_i_4387_);
v_b_4401_ = lean_array_fget_borrowed(v_bs_4386_, v_i_4387_);
v_sz_4402_ = lean_array_size(v_b_4401_);
v___x_4403_ = ((size_t)0ULL);
lean_inc(v_b_4401_);
v___x_4404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4383_, v_sz_4402_, v___x_4403_, v_b_4401_);
lean_inc_ref(v_f_4384_);
lean_inc(v___y_4392_);
lean_inc_ref(v___y_4391_);
lean_inc(v___y_4390_);
lean_inc_ref(v___y_4389_);
lean_inc(v_a_4400_);
v___x_4405_ = lean_apply_7(v_f_4384_, v_a_4400_, v___x_4404_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, lean_box(0));
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc(v_a_4406_);
lean_dec_ref(v___x_4405_);
v___x_4407_ = lean_unsigned_to_nat(1u);
v___x_4408_ = lean_nat_add(v_i_4387_, v___x_4407_);
lean_dec(v_i_4387_);
v___x_4409_ = lean_array_push(v_cs_4388_, v_a_4406_);
v_i_4387_ = v___x_4408_;
v_cs_4388_ = v___x_4409_;
goto _start;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec_ref(v_cs_4388_);
lean_dec(v_i_4387_);
lean_dec_ref(v_f_4384_);
v_a_4411_ = lean_ctor_get(v___x_4405_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4405_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4405_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4419_, lean_object* v_f_4420_, lean_object* v_as_4421_, lean_object* v_bs_4422_, lean_object* v_i_4423_, lean_object* v_cs_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4419_, v_f_4420_, v_as_4421_, v_bs_4422_, v_i_4423_, v_cs_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec_ref(v_bs_4422_);
lean_dec_ref(v_as_4421_);
lean_dec_ref(v_xs_4419_);
return v_res_4430_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Array_instInhabited(lean_box(0));
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; lean_object* v_toApplicative_4439_; lean_object* v_toFunctor_4440_; lean_object* v_toSeq_4441_; lean_object* v_toSeqLeft_4442_; lean_object* v_toSeqRight_4443_; lean_object* v___f_4444_; lean_object* v___f_4445_; lean_object* v___f_4446_; lean_object* v___f_4447_; lean_object* v___x_4448_; lean_object* v___f_4449_; lean_object* v___f_4450_; lean_object* v___f_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v_toApplicative_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4486_; 
v___x_4438_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4439_ = lean_ctor_get(v___x_4438_, 0);
v_toFunctor_4440_ = lean_ctor_get(v_toApplicative_4439_, 0);
v_toSeq_4441_ = lean_ctor_get(v_toApplicative_4439_, 2);
v_toSeqLeft_4442_ = lean_ctor_get(v_toApplicative_4439_, 3);
v_toSeqRight_4443_ = lean_ctor_get(v_toApplicative_4439_, 4);
v___f_4444_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4445_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4440_, 2);
v___f_4446_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4446_, 0, v_toFunctor_4440_);
v___f_4447_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4447_, 0, v_toFunctor_4440_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___f_4446_);
lean_ctor_set(v___x_4448_, 1, v___f_4447_);
lean_inc(v_toSeqRight_4443_);
v___f_4449_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4449_, 0, v_toSeqRight_4443_);
lean_inc(v_toSeqLeft_4442_);
v___f_4450_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4450_, 0, v_toSeqLeft_4442_);
lean_inc(v_toSeq_4441_);
v___f_4451_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4451_, 0, v_toSeq_4441_);
v___x_4452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4448_);
lean_ctor_set(v___x_4452_, 1, v___f_4444_);
lean_ctor_set(v___x_4452_, 2, v___f_4451_);
lean_ctor_set(v___x_4452_, 3, v___f_4450_);
lean_ctor_set(v___x_4452_, 4, v___f_4449_);
v___x_4453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4452_);
lean_ctor_set(v___x_4453_, 1, v___f_4445_);
v___x_4454_ = l_StateRefT_x27_instMonad___redArg(v___x_4453_);
v_toApplicative_4455_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4486_ == 0)
{
lean_object* v_unused_4487_; 
v_unused_4487_ = lean_ctor_get(v___x_4454_, 1);
lean_dec(v_unused_4487_);
v___x_4457_ = v___x_4454_;
v_isShared_4458_ = v_isSharedCheck_4486_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_toApplicative_4455_);
lean_dec(v___x_4454_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4486_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v_toFunctor_4459_; lean_object* v_toSeq_4460_; lean_object* v_toSeqLeft_4461_; lean_object* v_toSeqRight_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4484_; 
v_toFunctor_4459_ = lean_ctor_get(v_toApplicative_4455_, 0);
v_toSeq_4460_ = lean_ctor_get(v_toApplicative_4455_, 2);
v_toSeqLeft_4461_ = lean_ctor_get(v_toApplicative_4455_, 3);
v_toSeqRight_4462_ = lean_ctor_get(v_toApplicative_4455_, 4);
v_isSharedCheck_4484_ = !lean_is_exclusive(v_toApplicative_4455_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; 
v_unused_4485_ = lean_ctor_get(v_toApplicative_4455_, 1);
lean_dec(v_unused_4485_);
v___x_4464_ = v_toApplicative_4455_;
v_isShared_4465_ = v_isSharedCheck_4484_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_toSeqRight_4462_);
lean_inc(v_toSeqLeft_4461_);
lean_inc(v_toSeq_4460_);
lean_inc(v_toFunctor_4459_);
lean_dec(v_toApplicative_4455_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4484_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___f_4466_; lean_object* v___f_4467_; lean_object* v___f_4468_; lean_object* v___f_4469_; lean_object* v___x_4470_; lean_object* v___f_4471_; lean_object* v___f_4472_; lean_object* v___f_4473_; lean_object* v___x_4475_; 
v___f_4466_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4467_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4459_);
v___f_4468_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4468_, 0, v_toFunctor_4459_);
v___f_4469_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4469_, 0, v_toFunctor_4459_);
v___x_4470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___f_4468_);
lean_ctor_set(v___x_4470_, 1, v___f_4469_);
v___f_4471_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4471_, 0, v_toSeqRight_4462_);
v___f_4472_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4472_, 0, v_toSeqLeft_4461_);
v___f_4473_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4473_, 0, v_toSeq_4460_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set(v___x_4464_, 4, v___f_4471_);
lean_ctor_set(v___x_4464_, 3, v___f_4472_);
lean_ctor_set(v___x_4464_, 2, v___f_4473_);
lean_ctor_set(v___x_4464_, 1, v___f_4466_);
lean_ctor_set(v___x_4464_, 0, v___x_4470_);
v___x_4475_ = v___x_4464_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4470_);
lean_ctor_set(v_reuseFailAlloc_4483_, 1, v___f_4466_);
lean_ctor_set(v_reuseFailAlloc_4483_, 2, v___f_4473_);
lean_ctor_set(v_reuseFailAlloc_4483_, 3, v___f_4472_);
lean_ctor_set(v_reuseFailAlloc_4483_, 4, v___f_4471_);
v___x_4475_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4477_; 
if (v_isShared_4458_ == 0)
{
lean_ctor_set(v___x_4457_, 1, v___f_4467_);
lean_ctor_set(v___x_4457_, 0, v___x_4475_);
v___x_4477_ = v___x_4457_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4475_);
lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___f_4467_);
v___x_4477_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_940__overap_4480_; lean_object* v___x_4481_; 
v___x_4478_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4479_ = l_instInhabitedOfMonad___redArg(v___x_4477_, v___x_4478_);
v___x_940__overap_4480_ = lean_panic_fn_borrowed(v___x_4479_, v_msg_4432_);
lean_dec(v___x_4479_);
lean_inc(v___y_4436_);
lean_inc_ref(v___y_4435_);
lean_inc(v___y_4434_);
lean_inc_ref(v___y_4433_);
v___x_4481_ = lean_apply_5(v___x_940__overap_4480_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, lean_box(0));
return v___x_4481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v_res_4494_; 
v_res_4494_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
return v_res_4494_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4498_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4499_ = lean_unsigned_to_nat(2u);
v___x_4500_ = lean_unsigned_to_nat(73u);
v___x_4501_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4502_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4503_ = l_mkPanicMessageWithDecl(v___x_4502_, v___x_4501_, v___x_4500_, v___x_4499_, v___x_4498_);
return v___x_4503_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4505_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4506_ = lean_unsigned_to_nat(2u);
v___x_4507_ = lean_unsigned_to_nat(74u);
v___x_4508_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4509_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4510_ = l_mkPanicMessageWithDecl(v___x_4509_, v___x_4508_, v___x_4507_, v___x_4506_, v___x_4505_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4513_, lean_object* v_positions_4514_, lean_object* v_ys_4515_, lean_object* v_xs_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; uint8_t v___x_4524_; 
v___x_4522_ = lean_array_get_size(v_positions_4514_);
v___x_4523_ = lean_array_get_size(v_ys_4515_);
v___x_4524_ = lean_nat_dec_eq(v___x_4522_, v___x_4523_);
if (v___x_4524_ == 0)
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
lean_dec_ref(v_f_4513_);
v___x_4525_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4526_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4525_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
return v___x_4526_;
}
else
{
lean_object* v___x_4527_; lean_object* v___x_4528_; uint8_t v___x_4529_; 
v___x_4527_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4514_);
v___x_4528_ = lean_array_get_size(v_xs_4516_);
v___x_4529_ = lean_nat_dec_eq(v___x_4527_, v___x_4528_);
lean_dec(v___x_4527_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_dec_ref(v_f_4513_);
v___x_4530_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4531_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4530_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
return v___x_4531_;
}
else
{
lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4532_ = lean_unsigned_to_nat(0u);
v___x_4533_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4534_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4516_, v_f_4513_, v_ys_4515_, v_positions_4514_, v___x_4532_, v___x_4533_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
return v___x_4534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4535_, lean_object* v_positions_4536_, lean_object* v_ys_4537_, lean_object* v_xs_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4535_, v_positions_4536_, v_ys_4537_, v_xs_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v_xs_4538_);
lean_dec_ref(v_ys_4537_);
lean_dec_ref(v_positions_4536_);
return v_res_4544_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = l_Lean_Level_ofNat(v___x_4546_);
return v___x_4547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4548_, lean_object* v_positions_4549_, lean_object* v_motives_4550_, uint8_t v_isIndPred_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_){
_start:
{
lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v_indGroupInst_4560_; lean_object* v_brecOnUniv_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; 
v___x_4557_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4558_ = lean_unsigned_to_nat(0u);
v___x_4559_ = lean_array_get_borrowed(v___x_4557_, v_recArgInfos_4548_, v___x_4558_);
v_indGroupInst_4560_ = lean_ctor_get(v___x_4559_, 4);
if (v_isIndPred_4551_ == 0)
{
lean_object* v___f_4603_; lean_object* v___x_4604_; lean_object* v_motive_4605_; lean_object* v___x_4606_; 
v___f_4603_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4604_ = l_Lean_instInhabitedExpr;
v_motive_4605_ = lean_array_get_borrowed(v___x_4604_, v_motives_4550_, v___x_4558_);
lean_inc(v_motive_4605_);
v___x_4606_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4605_, v___f_4603_, v_isIndPred_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref(v___x_4606_);
v_brecOnUniv_4562_ = v_a_4607_;
v___y_4563_ = v_a_4552_;
v___y_4564_ = v_a_4553_;
v___y_4565_ = v_a_4554_;
v___y_4566_ = v_a_4555_;
goto v___jp_4561_;
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
v_a_4608_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4606_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4606_);
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
else
{
lean_object* v___x_4616_; 
v___x_4616_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4562_ = v___x_4616_;
v___y_4563_ = v_a_4552_;
v___y_4564_ = v_a_4553_;
v___y_4565_ = v_a_4554_;
v___y_4566_ = v_a_4555_;
goto v___jp_4561_;
}
v___jp_4561_:
{
lean_object* v_toIndGroupInfo_4567_; lean_object* v_levels_4568_; lean_object* v_params_4569_; lean_object* v___x_4570_; lean_object* v_brecOnCons_4571_; lean_object* v_brecOnAux_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
v_toIndGroupInfo_4567_ = lean_ctor_get(v_indGroupInst_4560_, 0);
v_levels_4568_ = lean_ctor_get(v_indGroupInst_4560_, 1);
v_params_4569_ = lean_ctor_get(v_indGroupInst_4560_, 2);
v___x_4570_ = lean_box(v_isIndPred_4551_);
lean_inc_n(v_levels_4568_, 2);
lean_inc(v_brecOnUniv_4562_);
lean_inc_ref(v_params_4569_);
lean_inc_ref(v_toIndGroupInfo_4567_);
v_brecOnCons_4571_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4571_, 0, v_toIndGroupInfo_4567_);
lean_closure_set(v_brecOnCons_4571_, 1, v_params_4569_);
lean_closure_set(v_brecOnCons_4571_, 2, v___x_4570_);
lean_closure_set(v_brecOnCons_4571_, 3, v_brecOnUniv_4562_);
lean_closure_set(v_brecOnCons_4571_, 4, v_levels_4568_);
v_brecOnAux_4572_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4567_, v_params_4569_, v_isIndPred_4551_, v_brecOnUniv_4562_, v_levels_4568_, v___x_4558_);
v___x_4573_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4567_);
v___x_4574_ = l_Lean_Meta_inferArgumentTypesN(v___x_4573_, v_brecOnAux_4572_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
if (lean_obj_tag(v___x_4574_) == 0)
{
lean_object* v_a_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v_a_4575_ = lean_ctor_get(v___x_4574_, 0);
lean_inc(v_a_4575_);
lean_dec_ref(v___x_4574_);
v___x_4576_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4577_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4576_, v_positions_4549_, v_a_4575_, v_motives_4550_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
lean_dec(v_a_4575_);
if (lean_obj_tag(v___x_4577_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4586_; 
v_a_4578_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4580_ = v___x_4577_;
v_isShared_4581_ = v_isSharedCheck_4586_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v___x_4577_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4586_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___f_4582_; lean_object* v___x_4584_; 
v___f_4582_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4582_, 0, v_brecOnCons_4571_);
lean_closure_set(v___f_4582_, 1, v_a_4578_);
if (v_isShared_4581_ == 0)
{
lean_ctor_set(v___x_4580_, 0, v___f_4582_);
v___x_4584_ = v___x_4580_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v___f_4582_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec_ref(v_brecOnCons_4571_);
v_a_4587_ = lean_ctor_get(v___x_4577_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4577_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4577_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
lean_dec_ref(v_brecOnCons_4571_);
v_a_4595_ = lean_ctor_get(v___x_4574_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4574_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4574_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4617_, lean_object* v_positions_4618_, lean_object* v_motives_4619_, lean_object* v_isIndPred_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_){
_start:
{
uint8_t v_isIndPred_boxed_4626_; lean_object* v_res_4627_; 
v_isIndPred_boxed_4626_ = lean_unbox(v_isIndPred_4620_);
v_res_4627_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4617_, v_positions_4618_, v_motives_4619_, v_isIndPred_boxed_4626_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec_ref(v_motives_4619_);
lean_dec_ref(v_positions_4618_);
lean_dec_ref(v_recArgInfos_4617_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4628_, lean_object* v_msg_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4636_, lean_object* v_msg_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4636_, v_msg_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4644_, lean_object* v_00_u03b1_4645_, lean_object* v_f_4646_, lean_object* v_positions_4647_, lean_object* v_ys_4648_, lean_object* v_xs_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v___x_4655_; 
v___x_4655_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4646_, v_positions_4647_, v_ys_4648_, v_xs_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
return v___x_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4656_, lean_object* v_00_u03b1_4657_, lean_object* v_f_4658_, lean_object* v_positions_4659_, lean_object* v_ys_4660_, lean_object* v_xs_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_res_4667_; 
v_res_4667_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4656_, v_00_u03b1_4657_, v_f_4658_, v_positions_4659_, v_ys_4660_, v_xs_4661_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
lean_dec(v___y_4665_);
lean_dec_ref(v___y_4664_);
lean_dec(v___y_4663_);
lean_dec_ref(v___y_4662_);
lean_dec_ref(v_xs_4661_);
lean_dec_ref(v_ys_4660_);
lean_dec_ref(v_positions_4659_);
return v_res_4667_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4668_, lean_object* v_00_u03b3_4669_, lean_object* v_xs_4670_, lean_object* v_f_4671_, lean_object* v_as_4672_, lean_object* v_bs_4673_, lean_object* v_i_4674_, lean_object* v_cs_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_){
_start:
{
lean_object* v___x_4681_; 
v___x_4681_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4670_, v_f_4671_, v_as_4672_, v_bs_4673_, v_i_4674_, v_cs_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4682_, lean_object* v_00_u03b3_4683_, lean_object* v_xs_4684_, lean_object* v_f_4685_, lean_object* v_as_4686_, lean_object* v_bs_4687_, lean_object* v_i_4688_, lean_object* v_cs_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v_res_4695_; 
v_res_4695_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4682_, v_00_u03b3_4683_, v_xs_4684_, v_f_4685_, v_as_4686_, v_bs_4687_, v_i_4688_, v_cs_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
lean_dec_ref(v_bs_4687_);
lean_dec_ref(v_as_4686_);
lean_dec_ref(v_xs_4684_);
return v_res_4695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v___x_4696_, lean_object* v_e_4697_){
_start:
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = l_Lean_indentD(v_e_4697_);
v___x_4699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4699_, 0, v___x_4696_);
lean_ctor_set(v___x_4699_, 1, v___x_4698_);
return v___x_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v_numTypeFormers_4700_, lean_object* v_x_4701_, lean_object* v_brecOnType_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4700_, v_brecOnType_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
return v___x_4708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed(lean_object* v_numTypeFormers_4709_, lean_object* v_x_4710_, lean_object* v_brecOnType_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(v_numTypeFormers_4709_, v_x_4710_, v_brecOnType_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec(v___y_4715_);
lean_dec_ref(v___y_4714_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec_ref(v_x_4710_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4718_, lean_object* v_as_4719_, size_t v_sz_4720_, size_t v_i_4721_, lean_object* v_b_4722_){
_start:
{
uint8_t v___x_4724_; 
v___x_4724_ = lean_usize_dec_lt(v_i_4721_, v_sz_4720_);
if (v___x_4724_ == 0)
{
lean_object* v___x_4725_; 
lean_dec_ref(v_a_4718_);
v___x_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4725_, 0, v_b_4722_);
return v___x_4725_;
}
else
{
lean_object* v_a_4726_; lean_object* v___x_4727_; size_t v___x_4728_; size_t v___x_4729_; 
v_a_4726_ = lean_array_uget_borrowed(v_as_4719_, v_i_4721_);
lean_inc_ref(v_a_4718_);
v___x_4727_ = lean_array_set(v_b_4722_, v_a_4726_, v_a_4718_);
v___x_4728_ = ((size_t)1ULL);
v___x_4729_ = lean_usize_add(v_i_4721_, v___x_4728_);
v_i_4721_ = v___x_4729_;
v_b_4722_ = v___x_4727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4731_, lean_object* v_as_4732_, lean_object* v_sz_4733_, lean_object* v_i_4734_, lean_object* v_b_4735_, lean_object* v___y_4736_){
_start:
{
size_t v_sz_boxed_4737_; size_t v_i_boxed_4738_; lean_object* v_res_4739_; 
v_sz_boxed_4737_ = lean_unbox_usize(v_sz_4733_);
lean_dec(v_sz_4733_);
v_i_boxed_4738_ = lean_unbox_usize(v_i_4734_);
lean_dec(v_i_4734_);
v_res_4739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4731_, v_as_4732_, v_sz_boxed_4737_, v_i_boxed_4738_, v_b_4735_);
lean_dec_ref(v_as_4732_);
return v_res_4739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_as_4740_, size_t v_sz_4741_, size_t v_i_4742_, lean_object* v_b_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
uint8_t v___x_4749_; 
v___x_4749_ = lean_usize_dec_lt(v_i_4742_, v_sz_4741_);
if (v___x_4749_ == 0)
{
lean_object* v___x_4750_; 
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v_b_4743_);
return v___x_4750_;
}
else
{
lean_object* v_snd_4751_; lean_object* v_fst_4752_; lean_object* v___x_4754_; uint8_t v_isShared_4755_; uint8_t v_isSharedCheck_4796_; 
v_snd_4751_ = lean_ctor_get(v_b_4743_, 1);
v_fst_4752_ = lean_ctor_get(v_b_4743_, 0);
v_isSharedCheck_4796_ = !lean_is_exclusive(v_b_4743_);
if (v_isSharedCheck_4796_ == 0)
{
v___x_4754_ = v_b_4743_;
v_isShared_4755_ = v_isSharedCheck_4796_;
goto v_resetjp_4753_;
}
else
{
lean_inc(v_snd_4751_);
lean_inc(v_fst_4752_);
lean_dec(v_b_4743_);
v___x_4754_ = lean_box(0);
v_isShared_4755_ = v_isSharedCheck_4796_;
goto v_resetjp_4753_;
}
v_resetjp_4753_:
{
lean_object* v_array_4756_; lean_object* v_start_4757_; lean_object* v_stop_4758_; uint8_t v___x_4759_; 
v_array_4756_ = lean_ctor_get(v_snd_4751_, 0);
v_start_4757_ = lean_ctor_get(v_snd_4751_, 1);
v_stop_4758_ = lean_ctor_get(v_snd_4751_, 2);
v___x_4759_ = lean_nat_dec_lt(v_start_4757_, v_stop_4758_);
if (v___x_4759_ == 0)
{
lean_object* v___x_4761_; 
if (v_isShared_4755_ == 0)
{
v___x_4761_ = v___x_4754_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_fst_4752_);
lean_ctor_set(v_reuseFailAlloc_4763_, 1, v_snd_4751_);
v___x_4761_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4762_; 
v___x_4762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4761_);
return v___x_4762_;
}
}
else
{
lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4792_; 
lean_inc(v_stop_4758_);
lean_inc(v_start_4757_);
lean_inc_ref(v_array_4756_);
v_isSharedCheck_4792_ = !lean_is_exclusive(v_snd_4751_);
if (v_isSharedCheck_4792_ == 0)
{
lean_object* v_unused_4793_; lean_object* v_unused_4794_; lean_object* v_unused_4795_; 
v_unused_4793_ = lean_ctor_get(v_snd_4751_, 2);
lean_dec(v_unused_4793_);
v_unused_4794_ = lean_ctor_get(v_snd_4751_, 1);
lean_dec(v_unused_4794_);
v_unused_4795_ = lean_ctor_get(v_snd_4751_, 0);
lean_dec(v_unused_4795_);
v___x_4765_ = v_snd_4751_;
v_isShared_4766_ = v_isSharedCheck_4792_;
goto v_resetjp_4764_;
}
else
{
lean_dec(v_snd_4751_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4792_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v_a_4767_; lean_object* v___x_4768_; size_t v_sz_4769_; size_t v___x_4770_; lean_object* v___x_4771_; 
v_a_4767_ = lean_array_uget_borrowed(v_as_4740_, v_i_4742_);
v___x_4768_ = lean_array_fget_borrowed(v_array_4756_, v_start_4757_);
v_sz_4769_ = lean_array_size(v___x_4768_);
v___x_4770_ = ((size_t)0ULL);
lean_inc(v_a_4767_);
v___x_4771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4767_, v___x_4768_, v_sz_4769_, v___x_4770_, v_fst_4752_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4776_; 
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
lean_inc(v_a_4772_);
lean_dec_ref(v___x_4771_);
v___x_4773_ = lean_unsigned_to_nat(1u);
v___x_4774_ = lean_nat_add(v_start_4757_, v___x_4773_);
lean_dec(v_start_4757_);
if (v_isShared_4766_ == 0)
{
lean_ctor_set(v___x_4765_, 1, v___x_4774_);
v___x_4776_ = v___x_4765_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_array_4756_);
lean_ctor_set(v_reuseFailAlloc_4783_, 1, v___x_4774_);
lean_ctor_set(v_reuseFailAlloc_4783_, 2, v_stop_4758_);
v___x_4776_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
lean_object* v___x_4778_; 
if (v_isShared_4755_ == 0)
{
lean_ctor_set(v___x_4754_, 1, v___x_4776_);
lean_ctor_set(v___x_4754_, 0, v_a_4772_);
v___x_4778_ = v___x_4754_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4772_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v___x_4776_);
v___x_4778_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
size_t v___x_4779_; size_t v___x_4780_; 
v___x_4779_ = ((size_t)1ULL);
v___x_4780_ = lean_usize_add(v_i_4742_, v___x_4779_);
v_i_4742_ = v___x_4780_;
v_b_4743_ = v___x_4778_;
goto _start;
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_del_object(v___x_4765_);
lean_dec(v_stop_4758_);
lean_dec(v_start_4757_);
lean_dec_ref(v_array_4756_);
lean_del_object(v___x_4754_);
v_a_4784_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4771_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4771_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_as_4797_, lean_object* v_sz_4798_, lean_object* v_i_4799_, lean_object* v_b_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
size_t v_sz_boxed_4806_; size_t v_i_boxed_4807_; lean_object* v_res_4808_; 
v_sz_boxed_4806_ = lean_unbox_usize(v_sz_4798_);
lean_dec(v_sz_4798_);
v_i_boxed_4807_ = lean_unbox_usize(v_i_4799_);
lean_dec(v_i_4799_);
v_res_4808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_as_4797_, v_sz_boxed_4806_, v_i_boxed_4807_, v_b_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec_ref(v_as_4797_);
return v_res_4808_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; 
v___x_4810_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4811_ = l_Lean_stringToMessageData(v___x_4810_);
return v___x_4811_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4812_; lean_object* v___f_4813_; 
v___x_4812_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4813_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0), 2, 1);
lean_closure_set(v___f_4813_, 0, v___x_4812_);
return v___f_4813_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4815_ = l_Lean_Expr_sort___override(v___x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4816_, lean_object* v_positions_4817_, lean_object* v_brecOnConst_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v_recArgInfo_4826_; lean_object* v_indicesPos_4827_; lean_object* v_indIdx_4828_; lean_object* v_brecOn_4829_; lean_object* v___f_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v___x_4824_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4825_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4826_ = lean_array_get_borrowed(v___x_4824_, v_recArgInfos_4816_, v___x_4825_);
v_indicesPos_4827_ = lean_ctor_get(v_recArgInfo_4826_, 3);
v_indIdx_4828_ = lean_ctor_get(v_recArgInfo_4826_, 5);
lean_inc(v_indIdx_4828_);
v_brecOn_4829_ = lean_apply_1(v_brecOnConst_4818_, v_indIdx_4828_);
v___f_4830_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4831_ = 0;
v___x_4832_ = lean_box(v___x_4831_);
lean_inc_ref(v_brecOn_4829_);
v___x_4833_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4833_, 0, v_brecOn_4829_);
lean_closure_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4833_, v___f_4830_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v___x_4835_; 
lean_dec_ref(v___x_4834_);
lean_inc(v_a_4822_);
lean_inc_ref(v_a_4821_);
lean_inc(v_a_4820_);
lean_inc_ref(v_a_4819_);
v___x_4835_ = lean_infer_type(v_brecOn_4829_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v_numTypeFormers_4837_; lean_object* v___f_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; uint8_t v___x_4843_; lean_object* v___x_4844_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref(v___x_4835_);
v_numTypeFormers_4837_ = lean_array_get_size(v_positions_4817_);
v___f_4838_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1___boxed), 8, 1);
lean_closure_set(v___f_4838_, 0, v_numTypeFormers_4837_);
v___x_4839_ = lean_array_get_size(v_indicesPos_4827_);
v___x_4840_ = lean_unsigned_to_nat(1u);
v___x_4841_ = lean_nat_add(v___x_4839_, v___x_4840_);
v___x_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
v___x_4843_ = 0;
v___x_4844_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkBRecOnF_spec__0___redArg(v_a_4836_, v___x_4842_, v___f_4838_, v___x_4843_, v___x_4843_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; size_t v_sz_4851_; size_t v___x_4852_; lean_object* v___x_4853_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc(v_a_4845_);
lean_dec_ref(v___x_4844_);
v___x_4846_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4817_);
v___x_4847_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4848_ = lean_mk_array(v___x_4846_, v___x_4847_);
v___x_4849_ = l_Array_toSubarray___redArg(v_positions_4817_, v___x_4825_, v_numTypeFormers_4837_);
v___x_4850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4848_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v_sz_4851_ = lean_array_size(v_a_4845_);
v___x_4852_ = ((size_t)0ULL);
v___x_4853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_a_4845_, v_sz_4851_, v___x_4852_, v___x_4850_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_);
lean_dec(v_a_4845_);
if (lean_obj_tag(v___x_4853_) == 0)
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4862_; 
v_a_4854_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4862_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4862_ == 0)
{
v___x_4856_ = v___x_4853_;
v_isShared_4857_ = v_isSharedCheck_4862_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4853_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4862_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v_fst_4858_; lean_object* v___x_4860_; 
v_fst_4858_ = lean_ctor_get(v_a_4854_, 0);
lean_inc(v_fst_4858_);
lean_dec(v_a_4854_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 0, v_fst_4858_);
v___x_4860_ = v___x_4856_;
goto v_reusejp_4859_;
}
else
{
lean_object* v_reuseFailAlloc_4861_; 
v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_fst_4858_);
v___x_4860_ = v_reuseFailAlloc_4861_;
goto v_reusejp_4859_;
}
v_reusejp_4859_:
{
return v___x_4860_;
}
}
}
else
{
lean_object* v_a_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4870_; 
v_a_4863_ = lean_ctor_get(v___x_4853_, 0);
v_isSharedCheck_4870_ = !lean_is_exclusive(v___x_4853_);
if (v_isSharedCheck_4870_ == 0)
{
v___x_4865_ = v___x_4853_;
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_a_4863_);
lean_dec(v___x_4853_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4870_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4868_; 
if (v_isShared_4866_ == 0)
{
v___x_4868_ = v___x_4865_;
goto v_reusejp_4867_;
}
else
{
lean_object* v_reuseFailAlloc_4869_; 
v_reuseFailAlloc_4869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
v___x_4868_ = v_reuseFailAlloc_4869_;
goto v_reusejp_4867_;
}
v_reusejp_4867_:
{
return v___x_4868_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4817_);
return v___x_4844_;
}
}
else
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
lean_dec_ref(v_positions_4817_);
v_a_4871_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4835_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4835_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
lean_dec_ref(v_brecOn_4829_);
lean_dec_ref(v_positions_4817_);
v_a_4879_ = lean_ctor_get(v___x_4834_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4834_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4834_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4834_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4887_, lean_object* v_positions_4888_, lean_object* v_brecOnConst_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4887_, v_positions_4888_, v_brecOnConst_4889_, v_a_4890_, v_a_4891_, v_a_4892_, v_a_4893_);
lean_dec(v_a_4893_);
lean_dec_ref(v_a_4892_);
lean_dec(v_a_4891_);
lean_dec_ref(v_a_4890_);
lean_dec_ref(v_recArgInfos_4887_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4896_, lean_object* v_as_4897_, size_t v_sz_4898_, size_t v_i_4899_, lean_object* v_b_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_){
_start:
{
lean_object* v___x_4906_; 
v___x_4906_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4896_, v_as_4897_, v_sz_4898_, v_i_4899_, v_b_4900_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4907_, lean_object* v_as_4908_, lean_object* v_sz_4909_, lean_object* v_i_4910_, lean_object* v_b_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
size_t v_sz_boxed_4917_; size_t v_i_boxed_4918_; lean_object* v_res_4919_; 
v_sz_boxed_4917_ = lean_unbox_usize(v_sz_4909_);
lean_dec(v_sz_4909_);
v_i_boxed_4918_ = lean_unbox_usize(v_i_4910_);
lean_dec(v_i_4910_);
v_res_4919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4907_, v_as_4908_, v_sz_boxed_4917_, v_i_boxed_4918_, v_b_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_);
lean_dec(v___y_4915_);
lean_dec_ref(v___y_4914_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec_ref(v_as_4908_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4920_, lean_object* v_a_4921_){
_start:
{
if (lean_obj_tag(v_a_4920_) == 0)
{
lean_object* v___x_4922_; 
v___x_4922_ = l_List_reverse___redArg(v_a_4921_);
return v___x_4922_;
}
else
{
lean_object* v_head_4923_; lean_object* v_tail_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4935_; 
v_head_4923_ = lean_ctor_get(v_a_4920_, 0);
v_tail_4924_ = lean_ctor_get(v_a_4920_, 1);
v_isSharedCheck_4935_ = !lean_is_exclusive(v_a_4920_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4926_ = v_a_4920_;
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_tail_4924_);
lean_inc(v_head_4923_);
lean_dec(v_a_4920_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4932_; 
v___x_4928_ = l_Nat_reprFast(v_head_4923_);
v___x_4929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
v___x_4930_ = l_Lean_MessageData_ofFormat(v___x_4929_);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 1, v_a_4921_);
lean_ctor_set(v___x_4926_, 0, v___x_4930_);
v___x_4932_ = v___x_4926_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v___x_4930_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v_a_4921_);
v___x_4932_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
v_a_4920_ = v_tail_4924_;
v_a_4921_ = v___x_4932_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4936_, lean_object* v_a_4937_){
_start:
{
if (lean_obj_tag(v_a_4936_) == 0)
{
lean_object* v___x_4938_; 
v___x_4938_ = l_List_reverse___redArg(v_a_4937_);
return v___x_4938_;
}
else
{
lean_object* v_head_4939_; lean_object* v_tail_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4952_; 
v_head_4939_ = lean_ctor_get(v_a_4936_, 0);
v_tail_4940_ = lean_ctor_get(v_a_4936_, 1);
v_isSharedCheck_4952_ = !lean_is_exclusive(v_a_4936_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4942_ = v_a_4936_;
v_isShared_4943_ = v_isSharedCheck_4952_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_tail_4940_);
lean_inc(v_head_4939_);
lean_dec(v_a_4936_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4952_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4944_ = lean_array_to_list(v_head_4939_);
v___x_4945_ = lean_box(0);
v___x_4946_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4944_, v___x_4945_);
v___x_4947_ = l_Lean_MessageData_ofList(v___x_4946_);
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 1, v_a_4937_);
lean_ctor_set(v___x_4942_, 0, v___x_4947_);
v___x_4949_ = v___x_4942_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4947_);
lean_ctor_set(v_reuseFailAlloc_4951_, 1, v_a_4937_);
v___x_4949_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
v_a_4936_ = v_tail_4940_;
v_a_4937_ = v___x_4949_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4953_, lean_object* v_v_4954_, lean_object* v_i_4955_){
_start:
{
lean_object* v___x_4956_; uint8_t v___x_4957_; 
v___x_4956_ = lean_array_get_size(v_xs_4953_);
v___x_4957_ = lean_nat_dec_lt(v_i_4955_, v___x_4956_);
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; 
lean_dec(v_i_4955_);
v___x_4958_ = lean_box(0);
return v___x_4958_;
}
else
{
lean_object* v___x_4959_; uint8_t v___x_4960_; 
v___x_4959_ = lean_array_fget_borrowed(v_xs_4953_, v_i_4955_);
v___x_4960_ = lean_nat_dec_eq(v___x_4959_, v_v_4954_);
if (v___x_4960_ == 0)
{
lean_object* v___x_4961_; lean_object* v___x_4962_; 
v___x_4961_ = lean_unsigned_to_nat(1u);
v___x_4962_ = lean_nat_add(v_i_4955_, v___x_4961_);
lean_dec(v_i_4955_);
v_i_4955_ = v___x_4962_;
goto _start;
}
else
{
lean_object* v___x_4964_; 
v___x_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4964_, 0, v_i_4955_);
return v___x_4964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4965_, lean_object* v_v_4966_, lean_object* v_i_4967_){
_start:
{
lean_object* v_res_4968_; 
v_res_4968_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4965_, v_v_4966_, v_i_4967_);
lean_dec(v_v_4966_);
lean_dec_ref(v_xs_4965_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4969_, lean_object* v_v_4970_){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = lean_unsigned_to_nat(0u);
v___x_4972_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4969_, v_v_4970_, v___x_4971_);
return v___x_4972_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4973_, lean_object* v_v_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4973_, v_v_4974_);
lean_dec(v_v_4974_);
lean_dec_ref(v_xs_4973_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4979_, lean_object* v_as_4980_, size_t v_sz_4981_, size_t v_i_4982_, lean_object* v_b_4983_){
_start:
{
uint8_t v___x_4984_; 
v___x_4984_ = lean_usize_dec_lt(v_i_4982_, v_sz_4981_);
if (v___x_4984_ == 0)
{
lean_inc_ref(v_b_4983_);
return v_b_4983_;
}
else
{
lean_object* v___x_4985_; lean_object* v_a_4986_; lean_object* v___x_4987_; 
v___x_4985_ = lean_box(0);
v_a_4986_ = lean_array_uget_borrowed(v_as_4980_, v_i_4982_);
v___x_4987_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4986_, v_fnIdx_4979_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v___x_4988_; size_t v___x_4989_; size_t v___x_4990_; 
v___x_4988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4989_ = ((size_t)1ULL);
v___x_4990_ = lean_usize_add(v_i_4982_, v___x_4989_);
v_i_4982_ = v___x_4990_;
v_b_4983_ = v___x_4988_;
goto _start;
}
else
{
lean_object* v_val_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5003_; 
v_val_4992_ = lean_ctor_get(v___x_4987_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4994_ = v___x_4987_;
v_isShared_4995_ = v_isSharedCheck_5003_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_val_4992_);
lean_dec(v___x_4987_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5003_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4999_; 
v___x_4996_ = lean_array_get_size(v_a_4986_);
v___x_4997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4996_);
lean_ctor_set(v___x_4997_, 1, v_val_4992_);
if (v_isShared_4995_ == 0)
{
lean_ctor_set(v___x_4994_, 0, v___x_4997_);
v___x_4999_ = v___x_4994_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5002_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_5000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
v___x_5001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_5000_);
lean_ctor_set(v___x_5001_, 1, v___x_4985_);
return v___x_5001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_5004_, lean_object* v_as_5005_, lean_object* v_sz_5006_, lean_object* v_i_5007_, lean_object* v_b_5008_){
_start:
{
size_t v_sz_boxed_5009_; size_t v_i_boxed_5010_; lean_object* v_res_5011_; 
v_sz_boxed_5009_ = lean_unbox_usize(v_sz_5006_);
lean_dec(v_sz_5006_);
v_i_boxed_5010_ = lean_unbox_usize(v_i_5007_);
lean_dec(v_i_5007_);
v_res_5011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5004_, v_as_5005_, v_sz_boxed_5009_, v_i_boxed_5010_, v_b_5008_);
lean_dec_ref(v_b_5008_);
lean_dec_ref(v_as_5005_);
lean_dec(v_fnIdx_5004_);
return v_res_5011_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5013_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_5014_ = l_Lean_stringToMessageData(v___x_5013_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_5015_, lean_object* v_positions_5016_, lean_object* v_fnIdx_5017_, lean_object* v_brecOnConst_5018_, lean_object* v_packedFArgs_5019_, lean_object* v_funTypes_5020_, lean_object* v_ys_5021_, lean_object* v___value_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_){
_start:
{
lean_object* v___y_5029_; lean_object* v___y_5030_; lean_object* v___y_5031_; lean_object* v___y_5032_; lean_object* v___x_5046_; lean_object* v_fst_5047_; lean_object* v_snd_5048_; lean_object* v___x_5049_; size_t v_sz_5050_; size_t v___x_5051_; lean_object* v___x_5052_; lean_object* v_fst_5053_; 
lean_inc_ref(v_ys_5021_);
lean_inc_ref(v_recArgInfo_5015_);
v___x_5046_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_5015_, v_ys_5021_);
v_fst_5047_ = lean_ctor_get(v___x_5046_, 0);
lean_inc(v_fst_5047_);
v_snd_5048_ = lean_ctor_get(v___x_5046_, 1);
lean_inc(v_snd_5048_);
lean_dec_ref(v___x_5046_);
v___x_5049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5050_ = lean_array_size(v_positions_5016_);
v___x_5051_ = ((size_t)0ULL);
v___x_5052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5017_, v_positions_5016_, v_sz_5050_, v___x_5051_, v___x_5049_);
v_fst_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc(v_fst_5053_);
lean_dec_ref(v___x_5052_);
if (lean_obj_tag(v_fst_5053_) == 0)
{
lean_dec(v_snd_5048_);
lean_dec(v_fst_5047_);
lean_dec_ref(v_ys_5021_);
lean_dec_ref(v_brecOnConst_5018_);
lean_dec_ref(v_recArgInfo_5015_);
v___y_5029_ = v___y_5023_;
v___y_5030_ = v___y_5024_;
v___y_5031_ = v___y_5025_;
v___y_5032_ = v___y_5026_;
goto v___jp_5028_;
}
else
{
lean_object* v_val_5054_; 
v_val_5054_ = lean_ctor_get(v_fst_5053_, 0);
lean_inc(v_val_5054_);
lean_dec_ref(v_fst_5053_);
if (lean_obj_tag(v_val_5054_) == 1)
{
lean_object* v_val_5055_; lean_object* v_fst_5056_; lean_object* v_snd_5057_; lean_object* v_indIdx_5058_; lean_object* v_brecOn_5059_; lean_object* v_brecOn_5060_; lean_object* v_brecOn_5061_; lean_object* v___x_5062_; 
lean_dec(v_fnIdx_5017_);
lean_dec_ref(v_positions_5016_);
v_val_5055_ = lean_ctor_get(v_val_5054_, 0);
lean_inc(v_val_5055_);
lean_dec_ref(v_val_5054_);
v_fst_5056_ = lean_ctor_get(v_val_5055_, 0);
lean_inc(v_fst_5056_);
v_snd_5057_ = lean_ctor_get(v_val_5055_, 1);
lean_inc(v_snd_5057_);
lean_dec(v_val_5055_);
v_indIdx_5058_ = lean_ctor_get(v_recArgInfo_5015_, 5);
lean_inc(v_indIdx_5058_);
lean_dec_ref(v_recArgInfo_5015_);
v_brecOn_5059_ = lean_apply_1(v_brecOnConst_5018_, v_indIdx_5058_);
v_brecOn_5060_ = l_Lean_mkAppN(v_brecOn_5059_, v_fst_5047_);
lean_dec(v_fst_5047_);
v_brecOn_5061_ = l_Lean_mkAppN(v_brecOn_5060_, v_packedFArgs_5019_);
v___x_5062_ = l_Lean_Meta_PProdN_projM(v_fst_5056_, v_snd_5057_, v_brecOn_5061_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec(v_snd_5057_);
lean_dec(v_fst_5056_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; uint8_t v___x_5066_; lean_object* v___x_5067_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref(v___x_5062_);
v___x_5064_ = l_Lean_mkAppN(v_a_5063_, v_snd_5048_);
lean_dec(v_snd_5048_);
v___x_5065_ = 1;
v___x_5066_ = 1;
v___x_5067_ = l_Lean_Meta_mkLetFVars(v_funTypes_5020_, v___x_5064_, v___x_5065_, v___x_5065_, v___x_5066_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v_a_5068_; uint8_t v___x_5069_; lean_object* v___x_5070_; 
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_a_5068_);
lean_dec_ref(v___x_5067_);
v___x_5069_ = 0;
v___x_5070_ = l_Lean_Meta_mkLambdaFVars(v_ys_5021_, v_a_5068_, v___x_5069_, v___x_5065_, v___x_5069_, v___x_5065_, v___x_5066_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_);
lean_dec_ref(v_ys_5021_);
return v___x_5070_;
}
else
{
lean_dec_ref(v_ys_5021_);
return v___x_5067_;
}
}
else
{
lean_dec(v_snd_5048_);
lean_dec_ref(v_ys_5021_);
return v___x_5062_;
}
}
else
{
lean_dec(v_val_5054_);
lean_dec(v_snd_5048_);
lean_dec(v_fst_5047_);
lean_dec_ref(v_ys_5021_);
lean_dec_ref(v_brecOnConst_5018_);
lean_dec_ref(v_recArgInfo_5015_);
v___y_5029_ = v___y_5023_;
v___y_5030_ = v___y_5024_;
v___y_5031_ = v___y_5025_;
v___y_5032_ = v___y_5026_;
goto v___jp_5028_;
}
}
v___jp_5028_:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v___x_5033_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_5034_ = l_Nat_reprFast(v_fnIdx_5017_);
v___x_5035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5034_);
v___x_5036_ = l_Lean_MessageData_ofFormat(v___x_5035_);
v___x_5037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5033_);
lean_ctor_set(v___x_5037_, 1, v___x_5036_);
v___x_5038_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5037_);
lean_ctor_set(v___x_5039_, 1, v___x_5038_);
v___x_5040_ = lean_array_to_list(v_positions_5016_);
v___x_5041_ = lean_box(0);
v___x_5042_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5040_, v___x_5041_);
v___x_5043_ = l_Lean_MessageData_ofList(v___x_5042_);
v___x_5044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5039_);
lean_ctor_set(v___x_5044_, 1, v___x_5043_);
v___x_5045_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5044_, v___y_5029_, v___y_5030_, v___y_5031_, v___y_5032_);
return v___x_5045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5071_, lean_object* v_positions_5072_, lean_object* v_fnIdx_5073_, lean_object* v_brecOnConst_5074_, lean_object* v_packedFArgs_5075_, lean_object* v_funTypes_5076_, lean_object* v_ys_5077_, lean_object* v___value_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v_res_5084_; 
v_res_5084_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5071_, v_positions_5072_, v_fnIdx_5073_, v_brecOnConst_5074_, v_packedFArgs_5075_, v_funTypes_5076_, v_ys_5077_, v___value_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
lean_dec_ref(v___value_5078_);
lean_dec_ref(v_funTypes_5076_);
lean_dec_ref(v_packedFArgs_5075_);
return v_res_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5085_, lean_object* v_fnIdx_5086_, lean_object* v_brecOnConst_5087_, lean_object* v_packedFArgs_5088_, lean_object* v_funTypes_5089_, lean_object* v_recArgInfo_5090_, lean_object* v_value_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_, lean_object* v_a_5095_){
_start:
{
lean_object* v___f_5097_; uint8_t v___x_5098_; lean_object* v___x_5099_; 
v___f_5097_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5097_, 0, v_recArgInfo_5090_);
lean_closure_set(v___f_5097_, 1, v_positions_5085_);
lean_closure_set(v___f_5097_, 2, v_fnIdx_5086_);
lean_closure_set(v___f_5097_, 3, v_brecOnConst_5087_);
lean_closure_set(v___f_5097_, 4, v_packedFArgs_5088_);
lean_closure_set(v___f_5097_, 5, v_funTypes_5089_);
v___x_5098_ = 0;
v___x_5099_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5091_, v___f_5097_, v___x_5098_, v_a_5092_, v_a_5093_, v_a_5094_, v_a_5095_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5100_, lean_object* v_fnIdx_5101_, lean_object* v_brecOnConst_5102_, lean_object* v_packedFArgs_5103_, lean_object* v_funTypes_5104_, lean_object* v_recArgInfo_5105_, lean_object* v_value_5106_, lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5100_, v_fnIdx_5101_, v_brecOnConst_5102_, v_packedFArgs_5103_, v_funTypes_5104_, v_recArgInfo_5105_, v_value_5106_, v_a_5107_, v_a_5108_, v_a_5109_, v_a_5110_);
lean_dec(v_a_5110_);
lean_dec_ref(v_a_5109_);
lean_dec(v_a_5108_);
lean_dec_ref(v_a_5107_);
return v_res_5112_;
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
