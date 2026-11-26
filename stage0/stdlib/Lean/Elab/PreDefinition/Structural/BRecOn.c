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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27;
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_7_; lean_object* v_env_8_; uint8_t v___x_9_; lean_object* v_env_10_; lean_object* v___x_11_; lean_object* v_toCold_12_; lean_object* v_mctx_13_; lean_object* v_lctx_14_; lean_object* v_options_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_7_ = lean_st_ref_get(v___y_5_);
v_env_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc_ref(v_env_8_);
lean_dec(v___x_7_);
v___x_9_ = 0;
v_env_10_ = l_Lean_Environment_setRecordingDeps(v_env_8_, v___x_9_);
v___x_11_ = lean_st_ref_get(v___y_3_);
v_toCold_12_ = lean_ctor_get(v___y_4_, 0);
v_mctx_13_ = lean_ctor_get(v___x_11_, 0);
lean_inc_ref(v_mctx_13_);
lean_dec(v___x_11_);
v_lctx_14_ = lean_ctor_get(v___y_2_, 2);
v_options_15_ = lean_ctor_get(v_toCold_12_, 2);
lean_inc_ref(v_options_15_);
lean_inc_ref(v_lctx_14_);
v___x_16_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_16_, 0, v_env_10_);
lean_ctor_set(v___x_16_, 1, v_mctx_13_);
lean_ctor_set(v___x_16_, 2, v_lctx_14_);
lean_ctor_set(v___x_16_, 3, v_options_15_);
v___x_17_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_msgData_1_);
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0___boxed(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(lean_object* v_msg_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_ref_32_; lean_object* v___x_33_; lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_42_; 
v_ref_32_ = lean_ctor_get(v___y_29_, 2);
v___x_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_);
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_42_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_42_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_ref_32_);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v_ref_32_);
lean_ctor_set(v___x_38_, 1, v_a_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set_tag(v___x_36_, 1);
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg___boxed(lean_object* v_msg_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_49_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__0));
v___x_52_ = l_Lean_stringToMessageData(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1);
v___x_59_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_58_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___boxed(lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_60_, v_a_61_, v_a_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(lean_object* v_00_u03b1_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_67_, v_a_68_, v_a_69_, v_a_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___boxed(lean_object* v_00_u03b1_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(v_00_u03b1_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(lean_object* v_00_u03b1_80_, lean_object* v_msg_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___boxed(lean_object* v_00_u03b1_88_, lean_object* v_msg_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(v_00_u03b1_88_, v_msg_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg(lean_object* v_e_104_, lean_object* v_F_105_, lean_object* v_k_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_112_; 
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
lean_inc_ref(v_e_104_);
v___x_112_ = lean_whnf(v_e_104_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 1);
switch(lean_obj_tag(v_a_113_))
{
case 5:
{
lean_object* v_fn_114_; 
v_fn_114_ = lean_ctor_get(v_a_113_, 0);
lean_inc_ref(v_fn_114_);
if (lean_obj_tag(v_fn_114_) == 5)
{
lean_object* v_fn_115_; 
v_fn_115_ = lean_ctor_get(v_fn_114_, 0);
if (lean_obj_tag(v_fn_115_) == 4)
{
lean_object* v_declName_116_; 
v_declName_116_ = lean_ctor_get(v_fn_115_, 0);
lean_inc(v_declName_116_);
if (lean_obj_tag(v_declName_116_) == 1)
{
lean_object* v_pre_117_; 
v_pre_117_ = lean_ctor_get(v_declName_116_, 0);
if (lean_obj_tag(v_pre_117_) == 0)
{
lean_object* v_arg_118_; lean_object* v_arg_119_; lean_object* v_str_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v_arg_118_ = lean_ctor_get(v_a_113_, 1);
lean_inc_ref(v_arg_118_);
lean_dec_ref_known(v_a_113_, 2);
v_arg_119_ = lean_ctor_get(v_fn_114_, 1);
lean_inc_ref(v_arg_119_);
lean_dec_ref_known(v_fn_114_, 2);
v_str_120_ = lean_ctor_get(v_declName_116_, 1);
lean_inc_ref(v_str_120_);
lean_dec_ref_known(v_declName_116_, 2);
v___x_121_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__0));
v___x_122_ = lean_string_dec_eq(v_str_120_, v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__1));
v___x_124_ = lean_string_dec_eq(v_str_120_, v___x_123_);
lean_dec_ref(v_str_120_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec_ref(v_arg_119_);
lean_dec_ref(v_arg_118_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_125_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec_ref(v_e_104_);
v___x_126_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__2));
v___x_127_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_105_);
v___x_128_ = l_Lean_Expr_proj___override(v___x_126_, v___x_127_, v_F_105_);
v___x_129_ = l_Lean_Meta_saveState___redArg(v_a_108_, v_a_110_);
if (lean_obj_tag(v___x_129_) == 0)
{
lean_object* v_a_130_; lean_object* v___x_131_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc(v_a_130_);
lean_dec_ref_known(v___x_129_, 1);
lean_inc_ref(v_k_106_);
v___x_131_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_119_, v___x_128_, v_k_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_dec(v_a_130_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_131_;
}
else
{
lean_object* v_a_132_; uint8_t v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v___x_133_ = l_Lean_Exception_isInterrupt(v_a_132_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
lean_inc(v_a_132_);
v___x_134_ = l_Lean_Exception_isRuntime(v_a_132_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_dec_ref_known(v___x_131_, 1);
v___x_135_ = l_Lean_Meta_SavedState_restore___redArg(v_a_130_, v_a_108_, v_a_110_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_136_; lean_object* v___x_137_; 
lean_dec_ref_known(v___x_135_, 1);
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = l_Lean_Expr_proj___override(v___x_126_, v___x_136_, v_F_105_);
v_e_104_ = v_arg_118_;
v_F_105_ = v___x_137_;
goto _start;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
v_a_139_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_135_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_135_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_dec(v_a_130_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_131_;
}
}
else
{
lean_dec(v_a_130_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_131_;
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v___x_128_);
lean_dec_ref(v_arg_119_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
v_a_147_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_129_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_129_);
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
lean_dec_ref(v_str_120_);
lean_dec_ref(v_e_104_);
v___x_155_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__3));
v___x_156_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_105_);
v___x_157_ = l_Lean_Expr_proj___override(v___x_155_, v___x_156_, v_F_105_);
v___x_158_ = l_Lean_Meta_saveState___redArg(v_a_108_, v_a_110_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
lean_inc_ref(v_k_106_);
v___x_160_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_119_, v___x_157_, v_k_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_dec(v_a_159_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_160_;
}
else
{
lean_object* v_a_161_; uint8_t v___x_162_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v___x_162_ = l_Lean_Exception_isInterrupt(v_a_161_);
if (v___x_162_ == 0)
{
uint8_t v___x_163_; 
lean_inc(v_a_161_);
v___x_163_ = l_Lean_Exception_isRuntime(v_a_161_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; 
lean_dec_ref_known(v___x_160_, 1);
v___x_164_ = l_Lean_Meta_SavedState_restore___redArg(v_a_159_, v_a_108_, v_a_110_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref_known(v___x_164_, 1);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = l_Lean_Expr_proj___override(v___x_155_, v___x_165_, v_F_105_);
v_e_104_ = v_arg_118_;
v_F_105_ = v___x_166_;
goto _start;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
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
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_160_;
}
}
else
{
lean_dec(v_a_159_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_160_;
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec_ref(v___x_157_);
lean_dec_ref(v_arg_119_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
v_a_176_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_158_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_158_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
else
{
lean_object* v___x_184_; 
lean_dec_ref_known(v_declName_116_, 2);
lean_dec_ref_known(v_fn_114_, 2);
lean_dec_ref_known(v_a_113_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_184_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_184_;
}
}
else
{
lean_object* v___x_185_; 
lean_dec(v_declName_116_);
lean_dec_ref_known(v_fn_114_, 2);
lean_dec_ref_known(v_a_113_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_185_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_185_;
}
}
else
{
lean_object* v___x_186_; 
lean_dec_ref_known(v_fn_114_, 2);
lean_dec_ref_known(v_a_113_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_186_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_186_;
}
}
else
{
lean_object* v___x_187_; 
lean_dec_ref_known(v_a_113_, 2);
lean_dec_ref(v_fn_114_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_187_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_187_;
}
}
case 4:
{
lean_object* v_declName_188_; 
v_declName_188_ = lean_ctor_get(v_a_113_, 0);
lean_inc(v_declName_188_);
lean_dec_ref_known(v_a_113_, 2);
if (lean_obj_tag(v_declName_188_) == 1)
{
lean_object* v_pre_189_; 
v_pre_189_ = lean_ctor_get(v_declName_188_, 0);
if (lean_obj_tag(v_pre_189_) == 0)
{
lean_object* v_str_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_str_190_ = lean_ctor_get(v_declName_188_, 1);
lean_inc_ref(v_str_190_);
lean_dec_ref_known(v_declName_188_, 2);
v___x_191_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__4));
v___x_192_ = lean_string_dec_eq(v_str_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__5));
v___x_194_ = lean_string_dec_eq(v_str_190_, v___x_193_);
lean_dec_ref(v_str_190_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_195_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_195_;
}
else
{
lean_object* v___x_196_; 
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
lean_dec_ref(v_e_104_);
v___x_196_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_196_;
}
}
else
{
lean_object* v___x_197_; 
lean_dec_ref(v_str_190_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
lean_dec_ref(v_e_104_);
v___x_197_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_197_;
}
}
else
{
lean_object* v___x_198_; 
lean_dec_ref_known(v_declName_188_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_198_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_198_;
}
}
else
{
lean_object* v___x_199_; 
lean_dec(v_declName_188_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_199_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_199_;
}
}
default: 
{
lean_object* v___x_200_; 
lean_dec(v_a_113_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_200_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_200_;
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
lean_dec_ref(v_e_104_);
v_a_201_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_112_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_112_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg___boxed(lean_object* v_e_209_, lean_object* v_F_210_, lean_object* v_k_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_209_, v_F_210_, v_k_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd(lean_object* v_00_u03b1_218_, lean_object* v_e_219_, lean_object* v_F_220_, lean_object* v_k_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_219_, v_F_220_, v_k_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___boxed(lean_object* v_00_u03b1_228_, lean_object* v_e_229_, lean_object* v_F_230_, lean_object* v_k_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Elab_Structural_searchPProd(v_00_u03b1_228_, v_e_229_, v_F_230_, v_k_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(lean_object* v_k_238_, lean_object* v_b_239_, lean_object* v_c_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; 
lean_inc(v___y_244_);
lean_inc_ref(v___y_243_);
lean_inc(v___y_242_);
lean_inc_ref(v___y_241_);
v___x_246_ = lean_apply_7(v_k_238_, v_b_239_, v_c_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, lean_box(0));
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_247_, lean_object* v_b_248_, lean_object* v_c_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(v_k_247_, v_b_248_, v_c_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(lean_object* v_type_256_, lean_object* v_k_257_, uint8_t v_cleanupAnnotations_258_, uint8_t v_whnfType_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___f_265_; lean_object* v___x_266_; 
v___f_265_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_265_, 0, v_k_257_);
v___x_266_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_256_, v___f_265_, v_cleanupAnnotations_258_, v_whnfType_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_a_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_266_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_266_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___boxed(lean_object* v_type_283_, lean_object* v_k_284_, lean_object* v_cleanupAnnotations_285_, lean_object* v_whnfType_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_292_; uint8_t v_whnfType_boxed_293_; lean_object* v_res_294_; 
v_cleanupAnnotations_boxed_292_ = lean_unbox(v_cleanupAnnotations_285_);
v_whnfType_boxed_293_ = lean_unbox(v_whnfType_286_);
v_res_294_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_283_, v_k_284_, v_cleanupAnnotations_boxed_292_, v_whnfType_boxed_293_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object* v_00_u03b1_295_, lean_object* v_type_296_, lean_object* v_k_297_, uint8_t v_cleanupAnnotations_298_, uint8_t v_whnfType_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_296_, v_k_297_, v_cleanupAnnotations_298_, v_whnfType_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object* v_00_u03b1_306_, lean_object* v_type_307_, lean_object* v_k_308_, lean_object* v_cleanupAnnotations_309_, lean_object* v_whnfType_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_316_; uint8_t v_whnfType_boxed_317_; lean_object* v_res_318_; 
v_cleanupAnnotations_boxed_316_ = lean_unbox(v_cleanupAnnotations_309_);
v_whnfType_boxed_317_ = lean_unbox(v_whnfType_310_);
v_res_318_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_00_u03b1_306_, v_type_307_, v_k_308_, v_cleanupAnnotations_boxed_316_, v_whnfType_boxed_317_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object* v_cls_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_toCold_328_; lean_object* v_options_329_; uint8_t v_hasTrace_330_; 
v_toCold_328_ = lean_ctor_get(v___y_325_, 0);
v_options_329_ = lean_ctor_get(v_toCold_328_, 2);
v_hasTrace_330_ = lean_ctor_get_uint8(v_options_329_, sizeof(void*)*1);
if (v_hasTrace_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_cls_322_);
v___x_331_ = lean_box(v_hasTrace_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
else
{
lean_object* v_inheritedTraceOptions_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_inheritedTraceOptions_333_ = lean_ctor_get(v_toCold_328_, 11);
v___x_334_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_335_ = l_Lean_Name_append(v___x_334_, v_cls_322_);
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
v_ref_358_ = lean_ctor_get(v___y_355_, 2);
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
lean_object* v___x_364_; lean_object* v_traceState_365_; lean_object* v_env_366_; lean_object* v_nextMacroScope_367_; lean_object* v_ngen_368_; lean_object* v_auxDeclNGen_369_; lean_object* v_cache_370_; lean_object* v_recordedDeps_371_; lean_object* v_messages_372_; lean_object* v_infoState_373_; lean_object* v_snapshotTasks_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_404_; 
v___x_364_ = lean_st_ref_take(v___y_356_);
v_traceState_365_ = lean_ctor_get(v___x_364_, 4);
v_env_366_ = lean_ctor_get(v___x_364_, 0);
v_nextMacroScope_367_ = lean_ctor_get(v___x_364_, 1);
v_ngen_368_ = lean_ctor_get(v___x_364_, 2);
v_auxDeclNGen_369_ = lean_ctor_get(v___x_364_, 3);
v_cache_370_ = lean_ctor_get(v___x_364_, 5);
v_recordedDeps_371_ = lean_ctor_get(v___x_364_, 6);
v_messages_372_ = lean_ctor_get(v___x_364_, 7);
v_infoState_373_ = lean_ctor_get(v___x_364_, 8);
v_snapshotTasks_374_ = lean_ctor_get(v___x_364_, 9);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_404_ == 0)
{
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_404_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_snapshotTasks_374_);
lean_inc(v_infoState_373_);
lean_inc(v_messages_372_);
lean_inc(v_recordedDeps_371_);
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
lean_object* v___x_383_; lean_object* v___x_384_; double v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_383_ = lean_box(0);
v___x_384_ = lean_box(0);
v___x_385_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_386_ = 0;
v___x_387_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_388_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_388_, 0, v_cls_351_);
lean_ctor_set(v___x_388_, 1, v___x_384_);
lean_ctor_set(v___x_388_, 2, v___x_387_);
lean_ctor_set_float(v___x_388_, sizeof(void*)*3, v___x_385_);
lean_ctor_set_float(v___x_388_, sizeof(void*)*3 + 8, v___x_385_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*3 + 16, v___x_386_);
v___x_389_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_390_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_388_);
lean_ctor_set(v___x_390_, 1, v_a_360_);
lean_ctor_set(v___x_390_, 2, v___x_389_);
lean_inc(v_ref_358_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v_ref_358_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_PersistentArray_push___redArg(v_traces_379_, v___x_391_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_392_);
v___x_394_ = v___x_381_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_392_);
lean_ctor_set_uint64(v_reuseFailAlloc_402_, sizeof(void*)*1, v_tid_378_);
v___x_394_ = v_reuseFailAlloc_402_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_396_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 4, v___x_394_);
v___x_396_ = v___x_376_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_env_366_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_nextMacroScope_367_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_ngen_368_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_auxDeclNGen_369_);
lean_ctor_set(v_reuseFailAlloc_401_, 4, v___x_394_);
lean_ctor_set(v_reuseFailAlloc_401_, 5, v_cache_370_);
lean_ctor_set(v_reuseFailAlloc_401_, 6, v_recordedDeps_371_);
lean_ctor_set(v_reuseFailAlloc_401_, 7, v_messages_372_);
lean_ctor_set(v_reuseFailAlloc_401_, 8, v_infoState_373_);
lean_ctor_set(v_reuseFailAlloc_401_, 9, v_snapshotTasks_374_);
v___x_396_ = v_reuseFailAlloc_401_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_st_ref_put(v___y_356_, v___x_396_);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_383_);
v___x_399_ = v___x_362_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_383_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v_a_420_, lean_object* v_C_421_, lean_object* v_cls_422_, lean_object* v___f_423_, lean_object* v_belowDict_424_, lean_object* v_F_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v___y_432_; lean_object* v___y_433_; lean_object* v___y_434_; lean_object* v___y_435_; lean_object* v___y_436_; lean_object* v___x_500_; 
lean_inc(v___y_429_);
lean_inc_ref(v___y_428_);
lean_inc(v___y_427_);
lean_inc_ref(v___y_426_);
v___x_500_ = lean_apply_5(v___f_423_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, lean_box(0));
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; uint8_t v___x_502_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
v___x_502_ = lean_unbox(v_a_501_);
lean_dec(v_a_501_);
if (v___x_502_ == 0)
{
goto v___jp_464_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_424_);
v___x_504_ = l_Lean_indentExpr(v_belowDict_424_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
lean_inc(v_cls_422_);
v___x_506_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_422_, v___x_505_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_dec_ref_known(v___x_506_, 1);
goto v___jp_464_;
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_422_);
lean_dec_ref(v_a_420_);
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_422_);
lean_dec_ref(v_a_420_);
v_a_515_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_500_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_500_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
v___jp_431_:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_isExprDefEq(v___y_432_, v_a_420_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
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
lean_object* v_fn_465_; lean_object* v_arg_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
lean_dec(v_cls_422_);
v_fn_465_ = lean_ctor_get(v_belowDict_424_, 0);
lean_inc_ref(v_fn_465_);
v_arg_466_ = lean_ctor_get(v_belowDict_424_, 1);
lean_inc_ref(v_arg_466_);
lean_dec_ref_known(v_belowDict_424_, 2);
v___x_467_ = l_Lean_Expr_getAppFn(v_fn_465_);
lean_dec_ref(v_fn_465_);
v___x_468_ = lean_expr_eqv(v___x_467_, v_C_421_);
lean_dec_ref(v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v_arg_466_);
lean_dec_ref(v_F_425_);
lean_dec_ref(v_a_420_);
v___x_469_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_426_, v___y_427_, v___y_428_, v___y_429_);
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
v___y_432_ = v_arg_466_;
v___y_433_ = v___y_426_;
v___y_434_ = v___y_427_;
v___y_435_ = v___y_428_;
v___y_436_ = v___y_429_;
goto v___jp_431_;
}
}
else
{
lean_object* v_toCold_478_; lean_object* v_options_479_; uint8_t v_hasTrace_480_; 
lean_dec_ref(v_F_425_);
lean_dec_ref(v_a_420_);
v_toCold_478_ = lean_ctor_get(v___y_428_, 0);
v_options_479_ = lean_ctor_get(v_toCold_478_, 2);
v_hasTrace_480_ = lean_ctor_get_uint8(v_options_479_, sizeof(void*)*1);
if (v_hasTrace_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_422_);
v___x_481_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_481_;
}
else
{
lean_object* v_inheritedTraceOptions_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_inheritedTraceOptions_482_ = lean_ctor_get(v_toCold_478_, 11);
v___x_483_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_422_);
v___x_484_ = l_Lean_Name_append(v___x_483_, v_cls_422_);
v___x_485_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_482_, v_options_479_, v___x_484_);
lean_dec(v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; 
lean_dec_ref(v_belowDict_424_);
lean_dec(v_cls_422_);
v___x_486_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_488_ = l_Lean_indentExpr(v_belowDict_424_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_422_, v___x_489_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v___x_491_; 
lean_dec_ref_known(v___x_490_, 1);
v___x_491_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_426_, v___y_427_, v___y_428_, v___y_429_);
return v___x_491_;
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_490_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v_a_523_, lean_object* v_C_524_, lean_object* v_cls_525_, lean_object* v___f_526_, lean_object* v_belowDict_527_, lean_object* v_F_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v_a_523_, v_C_524_, v_cls_525_, v___f_526_, v_belowDict_527_, v_F_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v_C_524_);
return v_res_534_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0(void){
_start:
{
lean_object* v___x_535_; lean_object* v_dummy_536_; 
v___x_535_ = lean_box(0);
v_dummy_536_ = l_Lean_Expr_sort___override(v___x_535_);
return v_dummy_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_537_, lean_object* v_C_538_, lean_object* v_cls_539_, lean_object* v___f_540_, lean_object* v_F_541_, lean_object* v_xs_542_, lean_object* v_belowDict_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___x_549_; lean_object* v___x_550_; 
v___x_549_ = 1;
v___x_550_ = l_Lean_Meta_zetaReduce(v_arg_537_, v___x_549_, v___x_549_, v___x_549_, v___y_544_, v___y_545_, v___y_546_, v___y_547_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___f_552_; lean_object* v_dummy_553_; lean_object* v_nargs_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc_n(v_a_551_, 2);
lean_dec_ref_known(v___x_550_, 1);
v___f_552_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_552_, 0, v_a_551_);
lean_closure_set(v___f_552_, 1, v_C_538_);
lean_closure_set(v___f_552_, 2, v_cls_539_);
lean_closure_set(v___f_552_, 3, v___f_540_);
v_dummy_553_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_554_ = l_Lean_Expr_getAppNumArgs(v_a_551_);
lean_inc(v_nargs_554_);
v___x_555_ = lean_mk_array(v_nargs_554_, v_dummy_553_);
v___x_556_ = lean_unsigned_to_nat(1u);
v___x_557_ = lean_nat_sub(v_nargs_554_, v___x_556_);
lean_dec(v_nargs_554_);
v___x_558_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_551_, v___x_555_, v___x_557_);
v___x_571_ = lean_array_get_size(v_xs_542_);
v___x_572_ = lean_array_get_size(v___x_558_);
v___x_573_ = lean_nat_dec_le(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref(v___x_558_);
lean_dec_ref(v___f_552_);
lean_dec_ref(v_F_541_);
v___x_574_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_544_, v___y_545_, v___y_546_, v___y_547_);
v_a_575_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_574_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_574_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
else
{
v___y_560_ = v___y_544_;
v___y_561_ = v___y_545_;
v___y_562_ = v___y_546_;
v___y_563_ = v___y_547_;
goto v___jp_559_;
}
v___jp_559_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_564_ = lean_array_get_size(v___x_558_);
v___x_565_ = lean_array_get_size(v_xs_542_);
v___x_566_ = lean_nat_sub(v___x_564_, v___x_565_);
v___x_567_ = l_Array_extract___redArg(v___x_558_, v___x_566_, v___x_564_);
lean_dec_ref(v___x_558_);
v___x_568_ = l_Lean_Expr_replaceFVars(v_belowDict_543_, v_xs_542_, v___x_567_);
v___x_569_ = l_Lean_mkAppN(v_F_541_, v___x_567_);
lean_dec_ref(v___x_567_);
v___x_570_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_568_, v___x_569_, v___f_552_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
return v___x_570_;
}
}
else
{
lean_dec_ref(v_F_541_);
lean_dec_ref(v___f_540_);
lean_dec(v_cls_539_);
lean_dec_ref(v_C_538_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_583_, lean_object* v_C_584_, lean_object* v_cls_585_, lean_object* v___f_586_, lean_object* v_F_587_, lean_object* v_xs_588_, lean_object* v_belowDict_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_583_, v_C_584_, v_cls_585_, v___f_586_, v_F_587_, v_xs_588_, v_belowDict_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec_ref(v_belowDict_589_);
lean_dec_ref(v_xs_588_);
return v_res_595_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0));
v___x_598_ = l_Lean_stringToMessageData(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v_arg_599_, lean_object* v_C_600_, lean_object* v_cls_601_, lean_object* v___f_602_, lean_object* v_belowDict_603_, lean_object* v_F_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___f_610_; lean_object* v___x_614_; 
lean_inc_ref(v___f_602_);
lean_inc(v_cls_601_);
v___f_610_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_610_, 0, v_arg_599_);
lean_closure_set(v___f_610_, 1, v_C_600_);
lean_closure_set(v___f_610_, 2, v_cls_601_);
lean_closure_set(v___f_610_, 3, v___f_602_);
lean_closure_set(v___f_610_, 4, v_F_604_);
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
v___x_614_ = lean_apply_5(v___f_602_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; uint8_t v___x_616_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = lean_unbox(v_a_615_);
lean_dec(v_a_615_);
if (v___x_616_ == 0)
{
lean_dec(v_cls_601_);
goto v___jp_611_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_617_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_603_);
v___x_618_ = l_Lean_indentExpr(v_belowDict_603_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_601_, v___x_619_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_dec_ref_known(v___x_620_, 1);
goto v___jp_611_;
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v___f_610_);
lean_dec_ref(v_belowDict_603_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref(v___f_610_);
lean_dec_ref(v_belowDict_603_);
lean_dec(v_cls_601_);
v_a_629_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_614_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_614_);
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
v___jp_611_:
{
uint8_t v___x_612_; lean_object* v___x_613_; 
v___x_612_ = 0;
v___x_613_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_603_, v___f_610_, v___x_612_, v___x_612_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v_arg_637_, lean_object* v_C_638_, lean_object* v_cls_639_, lean_object* v___f_640_, lean_object* v_belowDict_641_, lean_object* v_F_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v_arg_637_, v_C_638_, v_cls_639_, v___f_640_, v_belowDict_641_, v_F_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_648_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_664_, lean_object* v_belowDict_665_, lean_object* v_arg_666_, lean_object* v_F_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_cls_673_; lean_object* v___f_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v_a_677_; uint8_t v___x_678_; 
v_cls_673_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_674_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
lean_inc_ref(v_arg_666_);
v___f_675_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_675_, 0, v_arg_666_);
lean_closure_set(v___f_675_, 1, v_C_664_);
lean_closure_set(v___f_675_, 2, v_cls_673_);
lean_closure_set(v___f_675_, 3, v___f_674_);
v___x_676_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_673_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_676_);
v___x_678_ = lean_unbox(v_a_677_);
lean_dec(v_a_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec_ref(v_arg_666_);
v___x_679_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_665_, v_F_667_, v___f_675_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_679_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_680_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_665_);
v___x_681_ = l_Lean_indentExpr(v_belowDict_665_);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_indentExpr(v_arg_666_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_673_, v___x_686_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v___x_688_; 
lean_dec_ref_known(v___x_687_, 1);
v___x_688_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_665_, v_F_667_, v___f_675_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
return v___x_688_;
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec_ref(v___f_675_);
lean_dec_ref(v_F_667_);
lean_dec_ref(v_belowDict_665_);
v_a_689_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_687_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_697_, lean_object* v_belowDict_698_, lean_object* v_arg_699_, lean_object* v_F_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_697_, v_belowDict_698_, v_arg_699_, v_F_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v_t_707_, lean_object* v_x_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_t_707_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v_t_715_, lean_object* v_x_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v_t_715_, v_x_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec_ref(v_x_716_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___f_732_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_732_, 0, v_t_726_);
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1));
v___x_734_ = l_Lean_Core_mkFreshUserName(v___x_733_, v___y_729_, v___y_730_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_a_735_);
lean_ctor_set(v___x_739_, 1, v___f_732_);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_739_);
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v___f_732_);
v_a_744_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_734_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_734_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v___x_759_, lean_object* v_a_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_array_set(v___y_762_, v_a_760_, v___x_759_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v_x_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v___x_771_, v_a_772_, v_x_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v_a_772_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_781_, lean_object* v_a_782_, lean_object* v_x_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_snd_790_; lean_object* v_fst_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_842_; 
v_snd_790_ = lean_ctor_get(v___y_784_, 1);
v_fst_791_ = lean_ctor_get(v___y_784_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___y_784_);
if (v_isSharedCheck_842_ == 0)
{
v___x_793_ = v___y_784_;
v_isShared_794_ = v_isSharedCheck_842_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_snd_790_);
lean_inc(v_fst_791_);
lean_dec(v___y_784_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_842_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_array_795_; lean_object* v_start_796_; lean_object* v_stop_797_; uint8_t v___x_798_; 
v_array_795_ = lean_ctor_get(v_snd_790_, 0);
v_start_796_ = lean_ctor_get(v_snd_790_, 1);
v_stop_797_ = lean_ctor_get(v_snd_790_, 2);
v___x_798_ = lean_nat_dec_lt(v_start_796_, v_stop_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v_a_782_);
lean_dec_ref(v___x_781_);
if (v_isShared_794_ == 0)
{
v___x_800_ = v___x_793_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_fst_791_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_snd_790_);
v___x_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
else
{
lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_838_; 
lean_inc(v_stop_797_);
lean_inc(v_start_796_);
lean_inc_ref(v_array_795_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_snd_790_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; 
v_unused_839_ = lean_ctor_get(v_snd_790_, 2);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_snd_790_, 1);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_snd_790_, 0);
lean_dec(v_unused_841_);
v___x_805_ = v_snd_790_;
v_isShared_806_ = v_isSharedCheck_838_;
goto v_resetjp_804_;
}
else
{
lean_dec(v_snd_790_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_838_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_807_ = lean_array_fget_borrowed(v_array_795_, v_start_796_);
lean_inc(v___x_807_);
v___f_808_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_808_, 0, v___x_807_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_start_796_, v___x_809_);
lean_dec(v_start_796_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v___x_810_);
v___x_812_ = v___x_805_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_array_795_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_stop_797_);
v___x_812_ = v_reuseFailAlloc_837_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_9001__overap_815_; lean_object* v___x_816_; 
v_sz_813_ = lean_array_size(v_a_782_);
v___x_814_ = ((size_t)0ULL);
v___x_9001__overap_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_781_, v_a_782_, v___f_808_, v_sz_813_, v___x_814_, v_fst_791_);
lean_inc(v___y_788_);
lean_inc_ref(v___y_787_);
lean_inc(v___y_786_);
lean_inc_ref(v___y_785_);
v___x_816_ = lean_apply_5(v___x_9001__overap_815_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, lean_box(0));
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_828_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_828_ == 0)
{
v___x_819_ = v___x_816_;
v_isShared_820_ = v_isSharedCheck_828_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_816_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_828_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_812_);
lean_ctor_set(v___x_793_, 0, v_a_817_);
v___x_822_ = v___x_793_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_817_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_812_);
v___x_822_ = v_reuseFailAlloc_827_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_823_);
v___x_825_ = v___x_819_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v___x_812_);
lean_del_object(v___x_793_);
v_a_829_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_816_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_816_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_843_, lean_object* v_a_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_843_, v_a_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_toCold_859_; lean_object* v_options_860_; uint8_t v_hasTrace_861_; 
v_toCold_859_ = lean_ctor_get(v___y_856_, 0);
v_options_860_ = lean_ctor_get(v_toCold_859_, 2);
v_hasTrace_861_ = lean_ctor_get_uint8(v_options_860_, sizeof(void*)*1);
if (v_hasTrace_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v___x_853_);
v___x_862_ = lean_box(v_hasTrace_861_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
else
{
lean_object* v_inheritedTraceOptions_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_inheritedTraceOptions_864_ = lean_ctor_get(v_toCold_859_, 11);
v___x_865_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_866_ = l_Lean_Name_append(v___x_865_, v___x_853_);
v___x_867_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_864_, v_options_860_, v___x_866_);
lean_dec(v___x_866_);
v___x_868_ = lean_box(v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_876_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v_positions_890_, lean_object* v_a_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v_k_894_, lean_object* v___x_895_, lean_object* v___x_896_, lean_object* v_toMonadRef_897_, lean_object* v___x_898_, lean_object* v___f_899_, lean_object* v_Cs_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_9037__overap_907_; lean_object* v___x_908_; 
v___x_906_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_900_);
lean_inc_ref(v___x_888_);
v___x_9037__overap_907_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_888_, v___x_889_, v___x_906_, v_positions_890_, v_a_891_, v_Cs_900_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
v___x_908_ = lean_apply_5(v___x_9037__overap_907_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, lean_box(0));
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___x_951_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = l_Lean_mkAppN(v___x_892_, v_a_909_);
lean_dec(v_a_909_);
v___x_911_ = l_Subarray_copy___redArg(v___x_893_);
v___x_912_ = l_Lean_mkAppN(v___x_910_, v___x_911_);
lean_dec_ref(v___x_911_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
v___x_951_ = lean_apply_5(v___f_899_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, lean_box(0));
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; uint8_t v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_unbox(v_a_952_);
lean_dec(v_a_952_);
if (v___x_953_ == 0)
{
v___y_914_ = v___y_901_;
v___y_915_ = v___y_902_;
v___y_916_ = v___y_903_;
v___y_917_ = v___y_904_;
goto v___jp_913_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_9087__overap_965_; lean_object* v___x_966_; 
v___x_954_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_900_);
v___x_955_ = lean_array_to_list(v_Cs_900_);
v___x_956_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_957_ = lean_box(0);
v___x_958_ = l_List_mapTR_loop___redArg(v___x_956_, v___x_955_, v___x_957_);
v___x_959_ = l_Lean_MessageData_ofList(v___x_958_);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_954_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
lean_inc_ref(v___x_912_);
v___x_963_ = l_Lean_indentExpr(v___x_912_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
lean_inc(v___x_895_);
lean_inc_ref(v___x_898_);
lean_inc_ref(v_toMonadRef_897_);
lean_inc_ref(v___x_896_);
lean_inc_ref(v___x_888_);
v___x_9087__overap_965_ = l_Lean_addTrace___redArg(v___x_888_, v___x_896_, v_toMonadRef_897_, v___x_898_, v___x_895_, v___x_964_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
v___x_966_ = lean_apply_5(v___x_9087__overap_965_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, lean_box(0));
if (lean_obj_tag(v___x_966_) == 0)
{
lean_dec_ref_known(v___x_966_, 1);
v___y_914_ = v___y_901_;
v___y_915_ = v___y_902_;
v___y_916_ = v___y_903_;
v___y_917_ = v___y_904_;
goto v___jp_913_;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_Cs_900_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
lean_dec(v___x_895_);
lean_dec_ref(v_k_894_);
lean_dec_ref(v___x_888_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_Cs_900_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
lean_dec(v___x_895_);
lean_dec_ref(v_k_894_);
lean_dec_ref(v___x_888_);
v_a_975_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_951_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_951_);
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
v___jp_913_:
{
lean_object* v_toCold_918_; lean_object* v_options_919_; uint8_t v_hasTrace_920_; 
v_toCold_918_ = lean_ctor_get(v___y_916_, 0);
v_options_919_ = lean_ctor_get(v_toCold_918_, 2);
v_hasTrace_920_ = lean_ctor_get_uint8(v_options_919_, sizeof(void*)*1);
if (v_hasTrace_920_ == 0)
{
lean_object* v___x_921_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
lean_dec(v___x_895_);
lean_dec_ref(v___x_888_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_921_ = lean_apply_7(v_k_894_, v_Cs_900_, v___x_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
return v___x_921_;
}
else
{
lean_object* v_inheritedTraceOptions_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_inheritedTraceOptions_922_ = lean_ctor_get(v_toCold_918_, 11);
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_895_);
v___x_924_ = l_Lean_Name_append(v___x_923_, v___x_895_);
v___x_925_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_922_, v_options_919_, v___x_924_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
lean_dec(v___x_895_);
lean_dec_ref(v___x_888_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_926_ = lean_apply_7(v_k_894_, v_Cs_900_, v___x_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
return v___x_926_;
}
else
{
lean_object* v___x_927_; 
lean_inc_ref(v___x_912_);
v___x_927_ = l_Lean_Meta_isTypeCorrect(v___x_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
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
lean_object* v___x_930_; lean_object* v___x_9060__overap_931_; lean_object* v___x_932_; 
v___x_930_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_9060__overap_931_ = l_Lean_addTrace___redArg(v___x_888_, v___x_896_, v_toMonadRef_897_, v___x_898_, v___x_895_, v___x_930_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_932_ = lean_apply_5(v___x_9060__overap_931_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v___x_933_; 
lean_dec_ref_known(v___x_932_, 1);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_933_ = lean_apply_7(v_k_894_, v_Cs_900_, v___x_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
return v___x_933_;
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_Cs_900_);
lean_dec_ref(v_k_894_);
v_a_934_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_932_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_932_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v___x_942_; 
lean_dec_ref(v___x_898_);
lean_dec_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
lean_dec(v___x_895_);
lean_dec_ref(v___x_888_);
lean_inc(v___y_917_);
lean_inc_ref(v___y_916_);
lean_inc(v___y_915_);
lean_inc_ref(v___y_914_);
v___x_942_ = lean_apply_7(v_k_894_, v_Cs_900_, v___x_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, lean_box(0));
return v___x_942_;
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_Cs_900_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
lean_dec(v___x_895_);
lean_dec_ref(v_k_894_);
lean_dec_ref(v___x_888_);
v_a_943_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_927_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_927_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v_Cs_900_);
lean_dec_ref(v___f_899_);
lean_dec_ref(v___x_898_);
lean_dec_ref(v_toMonadRef_897_);
lean_dec_ref(v___x_896_);
lean_dec(v___x_895_);
lean_dec_ref(v_k_894_);
lean_dec_ref(v___x_893_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v___x_888_);
v_a_983_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_908_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_908_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_991_ = _args[0];
lean_object* v___x_992_ = _args[1];
lean_object* v_positions_993_ = _args[2];
lean_object* v_a_994_ = _args[3];
lean_object* v___x_995_ = _args[4];
lean_object* v___x_996_ = _args[5];
lean_object* v_k_997_ = _args[6];
lean_object* v___x_998_ = _args[7];
lean_object* v___x_999_ = _args[8];
lean_object* v_toMonadRef_1000_ = _args[9];
lean_object* v___x_1001_ = _args[10];
lean_object* v___f_1002_ = _args[11];
lean_object* v_Cs_1003_ = _args[12];
lean_object* v___y_1004_ = _args[13];
lean_object* v___y_1005_ = _args[14];
lean_object* v___y_1006_ = _args[15];
lean_object* v___y_1007_ = _args[16];
lean_object* v___y_1008_ = _args[17];
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_991_, v___x_992_, v_positions_993_, v_a_994_, v___x_995_, v___x_996_, v_k_997_, v___x_998_, v___x_999_, v_toMonadRef_1000_, v___x_1001_, v___f_1002_, v_Cs_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
return v_res_1009_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_unsigned_to_nat(37u);
v___x_1011_ = l_Lean_Level_ofNat(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1013_ = l_Lean_Expr_sort___override(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1020_, lean_object* v___x_1021_, lean_object* v___f_1022_, lean_object* v___f_1023_, lean_object* v___x_1024_, lean_object* v_numTypeFormers_1025_, lean_object* v___x_1026_, lean_object* v_k_1027_, lean_object* v___x_1028_, lean_object* v___x_1029_, lean_object* v_toMonadRef_1030_, lean_object* v___x_1031_, lean_object* v___f_1032_, lean_object* v_numIndParams_1033_, lean_object* v_a_1034_, lean_object* v_f_1035_, lean_object* v_args_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v_lower_1092_; lean_object* v_upper_1093_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___x_1159_; lean_object* v___x_1160_; uint8_t v___x_1161_; 
v___x_1159_ = lean_nat_add(v_numIndParams_1033_, v_numTypeFormers_1025_);
v___x_1160_ = lean_array_get_size(v_args_1036_);
v___x_1161_ = lean_nat_dec_lt(v___x_1159_, v___x_1160_);
lean_dec(v___x_1159_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
lean_dec_ref(v_args_1036_);
lean_dec_ref(v_f_1035_);
lean_dec(v_numIndParams_1033_);
lean_dec_ref(v_k_1027_);
lean_dec_ref(v___x_1026_);
lean_dec(v_numTypeFormers_1025_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___f_1022_);
lean_dec_ref(v_positions_1020_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1162_ = lean_apply_5(v___f_1032_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; uint8_t v___x_1164_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = lean_unbox(v_a_1163_);
lean_dec(v_a_1163_);
if (v___x_1164_ == 0)
{
lean_dec_ref(v_a_1034_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v_toMonadRef_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v___x_1028_);
lean_dec_ref(v___x_1021_);
v___y_1146_ = v___y_1037_;
v___y_1147_ = v___y_1038_;
v___y_1148_ = v___y_1039_;
v___y_1149_ = v___y_1040_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_9216__overap_1168_; lean_object* v___x_1169_; 
v___x_1165_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1166_ = l_Lean_indentExpr(v_a_1034_);
v___x_1167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1165_);
lean_ctor_set(v___x_1167_, 1, v___x_1166_);
v___x_9216__overap_1168_ = l_Lean_addTrace___redArg(v___x_1021_, v___x_1029_, v_toMonadRef_1030_, v___x_1031_, v___x_1028_, v___x_1167_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1169_ = lean_apply_5(v___x_9216__overap_1168_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_dec_ref_known(v___x_1169_, 1);
v___y_1146_ = v___y_1037_;
v___y_1147_ = v___y_1038_;
v___y_1148_ = v___y_1039_;
v___y_1149_ = v___y_1040_;
goto v___jp_1145_;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_a_1034_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v_toMonadRef_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v___x_1028_);
lean_dec_ref(v___x_1021_);
v_a_1178_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1162_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1162_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_dec_ref(v_a_1034_);
v___y_1136_ = v___y_1037_;
v___y_1137_ = v___y_1038_;
v___y_1138_ = v___y_1039_;
v___y_1139_ = v___y_1040_;
goto v___jp_1135_;
}
v___jp_1042_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; size_t v_sz_1056_; size_t v___x_1057_; lean_object* v___x_9132__overap_1058_; lean_object* v___x_1059_; 
v___x_1051_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1052_ = lean_mk_array(v___y_1045_, v___x_1051_);
v___x_1053_ = lean_array_get_size(v___y_1044_);
v___x_1054_ = l_Array_toSubarray___redArg(v___y_1044_, v___y_1046_, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1052_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v_sz_1056_ = lean_array_size(v_positions_1020_);
v___x_1057_ = ((size_t)0ULL);
lean_inc_ref(v___x_1021_);
v___x_9132__overap_1058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1021_, v_positions_1020_, v___f_1022_, v_sz_1056_, v___x_1057_, v___x_1055_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
v___x_1059_ = lean_apply_5(v___x_9132__overap_1058_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, lean_box(0));
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v_fst_1061_; size_t v_sz_1062_; lean_object* v___x_9135__overap_1063_; lean_object* v___x_1064_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v_fst_1061_ = lean_ctor_get(v_a_1060_, 0);
lean_inc(v_fst_1061_);
lean_dec(v_a_1060_);
v_sz_1062_ = lean_array_size(v_fst_1061_);
lean_inc_ref(v___x_1021_);
v___x_9135__overap_1063_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1021_, v___f_1023_, v_sz_1062_, v___x_1057_, v_fst_1061_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
v___x_1064_ = lean_apply_5(v___x_9135__overap_1063_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, lean_box(0));
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; uint8_t v___x_1066_; lean_object* v___x_9139__overap_1067_; lean_object* v___x_1068_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = 0;
v___x_9139__overap_1067_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1024_, v___x_1021_, v_a_1065_, v___y_1043_, v___x_1066_);
lean_inc(v___y_1050_);
lean_inc_ref(v___y_1049_);
lean_inc(v___y_1048_);
lean_inc_ref(v___y_1047_);
v___x_1068_ = lean_apply_5(v___x_9139__overap_1067_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, lean_box(0));
return v___x_1068_;
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v___x_1021_);
v_a_1069_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1064_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1064_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v___y_1043_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___x_1021_);
v_a_1077_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1059_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1059_);
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
v___jp_1085_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1094_ = l_Array_toSubarray___redArg(v_args_1036_, v_lower_1092_, v_upper_1093_);
v___x_1095_ = l_Subarray_copy___redArg(v___y_1091_);
v___x_1096_ = l_Lean_mkAppN(v_f_1035_, v___x_1095_);
lean_dec_ref(v___x_1095_);
lean_inc_ref(v___x_1096_);
v___x_1097_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1025_, v___x_1096_, v___y_1090_, v___y_1087_, v___y_1086_, v___y_1089_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_n(v_a_1098_, 2);
lean_dec_ref_known(v___x_1097_, 1);
lean_inc_ref(v___f_1032_);
lean_inc_ref(v___x_1031_);
lean_inc_ref(v_toMonadRef_1030_);
lean_inc_ref(v___x_1029_);
lean_inc(v___x_1028_);
lean_inc_ref(v_positions_1020_);
lean_inc_ref(v___x_1021_);
v___f_1099_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1099_, 0, v___x_1021_);
lean_closure_set(v___f_1099_, 1, v___x_1026_);
lean_closure_set(v___f_1099_, 2, v_positions_1020_);
lean_closure_set(v___f_1099_, 3, v_a_1098_);
lean_closure_set(v___f_1099_, 4, v___x_1096_);
lean_closure_set(v___f_1099_, 5, v___x_1094_);
lean_closure_set(v___f_1099_, 6, v_k_1027_);
lean_closure_set(v___f_1099_, 7, v___x_1028_);
lean_closure_set(v___f_1099_, 8, v___x_1029_);
lean_closure_set(v___f_1099_, 9, v_toMonadRef_1030_);
lean_closure_set(v___f_1099_, 10, v___x_1031_);
lean_closure_set(v___f_1099_, 11, v___f_1032_);
v___x_1100_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1020_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1090_);
v___x_1101_ = lean_apply_5(v___f_1032_, v___y_1090_, v___y_1087_, v___y_1086_, v___y_1089_, lean_box(0));
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; uint8_t v___x_1103_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = lean_unbox(v_a_1102_);
lean_dec(v_a_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v___x_1031_);
lean_dec_ref(v_toMonadRef_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v___x_1028_);
v___y_1043_ = v___f_1099_;
v___y_1044_ = v_a_1098_;
v___y_1045_ = v___x_1100_;
v___y_1046_ = v___y_1088_;
v___y_1047_ = v___y_1090_;
v___y_1048_ = v___y_1087_;
v___y_1049_ = v___y_1086_;
v___y_1050_ = v___y_1089_;
goto v___jp_1042_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_9171__overap_1109_; lean_object* v___x_1110_; 
v___x_1104_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1100_);
v___x_1105_ = l_Nat_reprFast(v___x_1100_);
v___x_1106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
v___x_1107_ = l_Lean_MessageData_ofFormat(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1104_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
lean_inc_ref(v___x_1021_);
v___x_9171__overap_1109_ = l_Lean_addTrace___redArg(v___x_1021_, v___x_1029_, v_toMonadRef_1030_, v___x_1031_, v___x_1028_, v___x_1108_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1086_);
lean_inc(v___y_1087_);
lean_inc_ref(v___y_1090_);
v___x_1110_ = lean_apply_5(v___x_9171__overap_1109_, v___y_1090_, v___y_1087_, v___y_1086_, v___y_1089_, lean_box(0));
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_dec_ref_known(v___x_1110_, 1);
v___y_1043_ = v___f_1099_;
v___y_1044_ = v_a_1098_;
v___y_1045_ = v___x_1100_;
v___y_1046_ = v___y_1088_;
v___y_1047_ = v___y_1090_;
v___y_1048_ = v___y_1087_;
v___y_1049_ = v___y_1086_;
v___y_1050_ = v___y_1089_;
goto v___jp_1042_;
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v___x_1100_);
lean_dec_ref(v___f_1099_);
lean_dec(v_a_1098_);
lean_dec(v___y_1088_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___f_1022_);
lean_dec_ref(v___x_1021_);
lean_dec_ref(v_positions_1020_);
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v___x_1100_);
lean_dec_ref(v___f_1099_);
lean_dec(v_a_1098_);
lean_dec(v___y_1088_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v_toMonadRef_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v___x_1028_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___f_1022_);
lean_dec_ref(v___x_1021_);
lean_dec_ref(v_positions_1020_);
v_a_1119_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1101_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1101_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec_ref(v___x_1096_);
lean_dec_ref(v___x_1094_);
lean_dec(v___y_1088_);
lean_dec_ref(v___f_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v_toMonadRef_1030_);
lean_dec_ref(v___x_1029_);
lean_dec(v___x_1028_);
lean_dec_ref(v_k_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v___f_1023_);
lean_dec_ref(v___f_1022_);
lean_dec_ref(v___x_1021_);
lean_dec_ref(v_positions_1020_);
v_a_1127_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1097_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1097_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
v___jp_1135_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1140_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1033_);
lean_inc_ref(v_args_1036_);
v___x_1141_ = l_Array_toSubarray___redArg(v_args_1036_, v___x_1140_, v_numIndParams_1033_);
v___x_1142_ = lean_nat_add(v_numIndParams_1033_, v_numTypeFormers_1025_);
lean_dec(v_numIndParams_1033_);
v___x_1143_ = lean_array_get_size(v_args_1036_);
v___x_1144_ = lean_nat_dec_le(v___x_1142_, v___x_1140_);
if (v___x_1144_ == 0)
{
v___y_1086_ = v___y_1138_;
v___y_1087_ = v___y_1137_;
v___y_1088_ = v___x_1140_;
v___y_1089_ = v___y_1139_;
v___y_1090_ = v___y_1136_;
v___y_1091_ = v___x_1141_;
v_lower_1092_ = v___x_1142_;
v_upper_1093_ = v___x_1143_;
goto v___jp_1085_;
}
else
{
lean_dec(v___x_1142_);
v___y_1086_ = v___y_1138_;
v___y_1087_ = v___y_1137_;
v___y_1088_ = v___x_1140_;
v___y_1089_ = v___y_1139_;
v___y_1090_ = v___y_1136_;
v___y_1091_ = v___x_1141_;
v_lower_1092_ = v___x_1140_;
v_upper_1093_ = v___x_1143_;
goto v___jp_1085_;
}
}
v___jp_1145_:
{
lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v___x_1150_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1186_ = _args[0];
lean_object* v___x_1187_ = _args[1];
lean_object* v___f_1188_ = _args[2];
lean_object* v___f_1189_ = _args[3];
lean_object* v___x_1190_ = _args[4];
lean_object* v_numTypeFormers_1191_ = _args[5];
lean_object* v___x_1192_ = _args[6];
lean_object* v_k_1193_ = _args[7];
lean_object* v___x_1194_ = _args[8];
lean_object* v___x_1195_ = _args[9];
lean_object* v_toMonadRef_1196_ = _args[10];
lean_object* v___x_1197_ = _args[11];
lean_object* v___f_1198_ = _args[12];
lean_object* v_numIndParams_1199_ = _args[13];
lean_object* v_a_1200_ = _args[14];
lean_object* v_f_1201_ = _args[15];
lean_object* v_args_1202_ = _args[16];
lean_object* v___y_1203_ = _args[17];
lean_object* v___y_1204_ = _args[18];
lean_object* v___y_1205_ = _args[19];
lean_object* v___y_1206_ = _args[20];
lean_object* v___y_1207_ = _args[21];
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1186_, v___x_1187_, v___f_1188_, v___f_1189_, v___x_1190_, v_numTypeFormers_1191_, v___x_1192_, v_k_1193_, v___x_1194_, v___x_1195_, v_toMonadRef_1196_, v___x_1197_, v___f_1198_, v_numIndParams_1199_, v_a_1200_, v_f_1201_, v_args_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1208_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_instMonadEIO___redArg();
return v___x_1209_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1211_ = l_StateRefT_x27_instMonad___redArg(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1218_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1219_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1220_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1219_, v___x_1218_);
return v___x_1220_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1222_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1223_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1222_, v___x_1221_);
return v___x_1223_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1226_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1228_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1229_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1228_, v___x_1227_, v___x_1226_);
return v___x_1229_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; 
v___x_1230_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1231_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1232_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1233_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1232_, v___f_1231_, v___x_1230_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1238_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1239_ = l_Lean_Name_append(v___x_1238_, v___x_1237_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17));
v___x_1242_ = l_Lean_stringToMessageData(v___x_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1243_, lean_object* v_numIndParams_1244_, lean_object* v_positions_1245_, lean_object* v_k_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v___x_1252_; lean_object* v_toApplicative_1253_; lean_object* v_toFunctor_1254_; lean_object* v_toSeq_1255_; lean_object* v_toSeqLeft_1256_; lean_object* v_toSeqRight_1257_; lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_toApplicative_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1397_; 
v___x_1252_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1253_ = lean_ctor_get(v___x_1252_, 0);
v_toFunctor_1254_ = lean_ctor_get(v_toApplicative_1253_, 0);
v_toSeq_1255_ = lean_ctor_get(v_toApplicative_1253_, 2);
v_toSeqLeft_1256_ = lean_ctor_get(v_toApplicative_1253_, 3);
v_toSeqRight_1257_ = lean_ctor_get(v_toApplicative_1253_, 4);
v___f_1258_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1254_, 2);
v___f_1260_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1260_, 0, v_toFunctor_1254_);
v___f_1261_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1261_, 0, v_toFunctor_1254_);
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___f_1260_);
lean_ctor_set(v___x_1262_, 1, v___f_1261_);
lean_inc(v_toSeqRight_1257_);
v___f_1263_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1263_, 0, v_toSeqRight_1257_);
lean_inc(v_toSeqLeft_1256_);
v___f_1264_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1264_, 0, v_toSeqLeft_1256_);
lean_inc(v_toSeq_1255_);
v___f_1265_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1265_, 0, v_toSeq_1255_);
v___x_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1262_);
lean_ctor_set(v___x_1266_, 1, v___f_1258_);
lean_ctor_set(v___x_1266_, 2, v___f_1265_);
lean_ctor_set(v___x_1266_, 3, v___f_1264_);
lean_ctor_set(v___x_1266_, 4, v___f_1263_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___f_1259_);
v___x_1268_ = l_StateRefT_x27_instMonad___redArg(v___x_1267_);
v_toApplicative_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1268_, 1);
lean_dec(v_unused_1398_);
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1397_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_toApplicative_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1397_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v_toFunctor_1273_; lean_object* v_toSeq_1274_; lean_object* v_toSeqLeft_1275_; lean_object* v_toSeqRight_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1395_; 
v_toFunctor_1273_ = lean_ctor_get(v_toApplicative_1269_, 0);
v_toSeq_1274_ = lean_ctor_get(v_toApplicative_1269_, 2);
v_toSeqLeft_1275_ = lean_ctor_get(v_toApplicative_1269_, 3);
v_toSeqRight_1276_ = lean_ctor_get(v_toApplicative_1269_, 4);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_toApplicative_1269_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; 
v_unused_1396_ = lean_ctor_get(v_toApplicative_1269_, 1);
lean_dec(v_unused_1396_);
v___x_1278_ = v_toApplicative_1269_;
v_isShared_1279_ = v_isSharedCheck_1395_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_toSeqRight_1276_);
lean_inc(v_toSeqLeft_1275_);
lean_inc(v_toSeq_1274_);
lean_inc(v_toFunctor_1273_);
lean_dec(v_toApplicative_1269_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1395_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___f_1280_; lean_object* v___f_1281_; lean_object* v___f_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___x_1289_; 
v___f_1280_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1281_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1273_);
v___f_1282_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1282_, 0, v_toFunctor_1273_);
v___f_1283_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1283_, 0, v_toFunctor_1273_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___f_1282_);
lean_ctor_set(v___x_1284_, 1, v___f_1283_);
v___f_1285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1285_, 0, v_toSeqRight_1276_);
v___f_1286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1286_, 0, v_toSeqLeft_1275_);
v___f_1287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1287_, 0, v_toSeq_1274_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 4, v___f_1285_);
lean_ctor_set(v___x_1278_, 3, v___f_1286_);
lean_ctor_set(v___x_1278_, 2, v___f_1287_);
lean_ctor_set(v___x_1278_, 1, v___f_1280_);
lean_ctor_set(v___x_1278_, 0, v___x_1284_);
v___x_1289_ = v___x_1278_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___f_1280_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v___f_1287_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v___f_1286_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v___f_1285_);
v___x_1289_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1291_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___f_1281_);
lean_ctor_set(v___x_1271_, 0, v___x_1289_);
v___x_1291_ = v___x_1271_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___f_1281_);
v___x_1291_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v_toApplicative_1293_; lean_object* v_toFunctor_1294_; lean_object* v_toSeq_1295_; lean_object* v_toSeqLeft_1296_; lean_object* v_toSeqRight_1297_; lean_object* v___f_1298_; lean_object* v___f_1299_; lean_object* v___x_1300_; lean_object* v___f_1301_; lean_object* v___f_1302_; lean_object* v___f_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_toMonadRef_1310_; lean_object* v___f_1311_; lean_object* v___f_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_numTypeFormers_1315_; lean_object* v___x_1316_; 
v___x_1292_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1293_ = lean_ctor_get(v___x_1252_, 0);
v_toFunctor_1294_ = lean_ctor_get(v_toApplicative_1293_, 0);
v_toSeq_1295_ = lean_ctor_get(v_toApplicative_1293_, 2);
v_toSeqLeft_1296_ = lean_ctor_get(v_toApplicative_1293_, 3);
v_toSeqRight_1297_ = lean_ctor_get(v_toApplicative_1293_, 4);
lean_inc_ref_n(v_toFunctor_1294_, 2);
v___f_1298_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1298_, 0, v_toFunctor_1294_);
v___f_1299_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1299_, 0, v_toFunctor_1294_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___f_1298_);
lean_ctor_set(v___x_1300_, 1, v___f_1299_);
lean_inc(v_toSeqRight_1297_);
v___f_1301_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1301_, 0, v_toSeqRight_1297_);
lean_inc(v_toSeqLeft_1296_);
v___f_1302_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1302_, 0, v_toSeqLeft_1296_);
lean_inc(v_toSeq_1295_);
v___f_1303_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1303_, 0, v_toSeq_1295_);
v___x_1304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1300_);
lean_ctor_set(v___x_1304_, 1, v___f_1258_);
lean_ctor_set(v___x_1304_, 2, v___f_1303_);
lean_ctor_set(v___x_1304_, 3, v___f_1302_);
lean_ctor_set(v___x_1304_, 4, v___f_1301_);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___f_1259_);
v___x_1306_ = l_StateRefT_x27_instMonad___redArg(v___x_1305_);
v___x_1307_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1307_, 0, lean_box(0));
lean_closure_set(v___x_1307_, 1, lean_box(0));
lean_closure_set(v___x_1307_, 2, v___x_1306_);
v___x_1308_ = l_instMonadControlTOfPure___redArg(v___x_1307_);
v___x_1309_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1310_ = lean_ctor_get(v___x_1309_, 0);
v___f_1311_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
lean_inc_ref(v___x_1291_);
v___f_1312_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_1312_, 0, v___x_1291_);
v___x_1313_ = l_Lean_instInhabitedExpr;
v___x_1314_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1315_ = lean_array_get_size(v_positions_1245_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
lean_inc_ref(v_below_1243_);
v___x_1316_ = lean_infer_type(v_below_1243_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___x_1369_; lean_object* v_a_1370_; uint8_t v___x_1371_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc_n(v_a_1317_, 2);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1319_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref(v_toMonadRef_1310_);
lean_inc_ref(v___x_1291_);
v___f_1320_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1320_, 0, v_positions_1245_);
lean_closure_set(v___f_1320_, 1, v___x_1291_);
lean_closure_set(v___f_1320_, 2, v___f_1312_);
lean_closure_set(v___f_1320_, 3, v___f_1311_);
lean_closure_set(v___f_1320_, 4, v___x_1308_);
lean_closure_set(v___f_1320_, 5, v_numTypeFormers_1315_);
lean_closure_set(v___f_1320_, 6, v___x_1313_);
lean_closure_set(v___f_1320_, 7, v_k_1246_);
lean_closure_set(v___f_1320_, 8, v___x_1318_);
lean_closure_set(v___f_1320_, 9, v___x_1292_);
lean_closure_set(v___f_1320_, 10, v_toMonadRef_1310_);
lean_closure_set(v___f_1320_, 11, v___x_1314_);
lean_closure_set(v___f_1320_, 12, v___f_1319_);
lean_closure_set(v___f_1320_, 13, v_numIndParams_1244_);
lean_closure_set(v___f_1320_, 14, v_a_1317_);
v___x_1369_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1318_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_);
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
v___x_1371_ = lean_unbox(v_a_1370_);
lean_dec(v_a_1370_);
if (v___x_1371_ == 0)
{
v___y_1334_ = v_a_1247_;
v___y_1335_ = v_a_1248_;
v___y_1336_ = v_a_1249_;
v___y_1337_ = v_a_1250_;
goto v___jp_1333_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_8829__overap_1375_; lean_object* v___x_1376_; 
v___x_1372_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18);
lean_inc(v_a_1317_);
v___x_1373_ = l_Lean_MessageData_ofExpr(v_a_1317_);
v___x_1374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1372_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
lean_inc_ref(v_toMonadRef_1310_);
lean_inc_ref(v___x_1291_);
v___x_8829__overap_1375_ = l_Lean_addTrace___redArg(v___x_1291_, v___x_1292_, v_toMonadRef_1310_, v___x_1314_, v___x_1318_, v___x_1374_);
lean_inc(v_a_1250_);
lean_inc_ref(v_a_1249_);
lean_inc(v_a_1248_);
lean_inc_ref(v_a_1247_);
v___x_1376_ = lean_apply_5(v___x_8829__overap_1375_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, lean_box(0));
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_dec_ref_known(v___x_1376_, 1);
v___y_1334_ = v_a_1247_;
v___y_1335_ = v_a_1248_;
v___y_1336_ = v_a_1249_;
v___y_1337_ = v_a_1250_;
goto v___jp_1333_;
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v___f_1320_);
lean_dec(v_a_1317_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v_below_1243_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
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
v___jp_1321_:
{
lean_object* v_dummy_1326_; lean_object* v_nargs_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_8825__overap_1331_; lean_object* v___x_1332_; 
v_dummy_1326_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1327_ = l_Lean_Expr_getAppNumArgs(v_a_1317_);
lean_inc(v_nargs_1327_);
v___x_1328_ = lean_mk_array(v_nargs_1327_, v_dummy_1326_);
v___x_1329_ = lean_unsigned_to_nat(1u);
v___x_1330_ = lean_nat_sub(v_nargs_1327_, v___x_1329_);
lean_dec(v_nargs_1327_);
v___x_8825__overap_1331_ = l_Lean_Expr_withAppAux___redArg(v___f_1320_, v_a_1317_, v___x_1328_, v___x_1330_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
v___x_1332_ = lean_apply_5(v___x_8825__overap_1331_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, lean_box(0));
return v___x_1332_;
}
v___jp_1333_:
{
lean_object* v_toCold_1338_; lean_object* v_options_1339_; uint8_t v_hasTrace_1340_; 
v_toCold_1338_ = lean_ctor_get(v___y_1336_, 0);
v_options_1339_ = lean_ctor_get(v_toCold_1338_, 2);
v_hasTrace_1340_ = lean_ctor_get_uint8(v_options_1339_, sizeof(void*)*1);
if (v_hasTrace_1340_ == 0)
{
lean_dec_ref(v___x_1291_);
lean_dec_ref(v_below_1243_);
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1336_;
v___y_1325_ = v___y_1337_;
goto v___jp_1321_;
}
else
{
lean_object* v_inheritedTraceOptions_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_inheritedTraceOptions_1341_ = lean_ctor_get(v_toCold_1338_, 11);
v___x_1342_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1343_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1341_, v_options_1339_, v___x_1342_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v___x_1291_);
lean_dec_ref(v_below_1243_);
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1336_;
v___y_1325_ = v___y_1337_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Meta_isTypeCorrect(v_below_1243_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; uint8_t v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
if (v___x_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v_a_1348_; uint8_t v___x_1349_; 
v___x_1347_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1318_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = lean_unbox(v_a_1348_);
lean_dec(v_a_1348_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v___x_1291_);
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1336_;
v___y_1325_ = v___y_1337_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1350_; lean_object* v___x_8827__overap_1351_; lean_object* v___x_1352_; 
v___x_1350_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1310_);
v___x_8827__overap_1351_ = l_Lean_addTrace___redArg(v___x_1291_, v___x_1292_, v_toMonadRef_1310_, v___x_1314_, v___x_1318_, v___x_1350_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1352_ = lean_apply_5(v___x_8827__overap_1351_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, lean_box(0));
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_dec_ref_known(v___x_1352_, 1);
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1336_;
v___y_1325_ = v___y_1337_;
goto v___jp_1321_;
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec_ref(v___f_1320_);
lean_dec(v_a_1317_);
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
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
lean_dec_ref(v___x_1291_);
v___y_1322_ = v___y_1334_;
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1336_;
v___y_1325_ = v___y_1337_;
goto v___jp_1321_;
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v___f_1320_);
lean_dec(v_a_1317_);
lean_dec_ref(v___x_1291_);
v_a_1361_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1344_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1344_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v___f_1312_);
lean_dec_ref(v___x_1308_);
lean_dec_ref(v___x_1291_);
lean_dec_ref(v_k_1246_);
lean_dec_ref(v_positions_1245_);
lean_dec(v_numIndParams_1244_);
lean_dec_ref(v_below_1243_);
v_a_1385_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1316_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1316_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1399_, lean_object* v_numIndParams_1400_, lean_object* v_positions_1401_, lean_object* v_k_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1399_, v_numIndParams_1400_, v_positions_1401_, v_k_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1409_, lean_object* v_inst_1410_, lean_object* v_below_1411_, lean_object* v_numIndParams_1412_, lean_object* v_positions_1413_, lean_object* v_k_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1411_, v_numIndParams_1412_, v_positions_1413_, v_k_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_inst_1422_, lean_object* v_below_1423_, lean_object* v_numIndParams_1424_, lean_object* v_positions_1425_, lean_object* v_k_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1421_, v_inst_1422_, v_below_1423_, v_numIndParams_1424_, v_positions_1425_, v_k_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_inst_1422_);
return v_res_1432_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = lean_unsigned_to_nat(32u);
v___x_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1436_ = ((size_t)5ULL);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = lean_unsigned_to_nat(32u);
v___x_1439_ = lean_mk_empty_array_with_capacity(v___x_1438_);
v___x_1440_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1441_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___x_1439_);
lean_ctor_set(v___x_1441_, 2, v___x_1437_);
lean_ctor_set(v___x_1441_, 3, v___x_1437_);
lean_ctor_set_usize(v___x_1441_, 4, v___x_1436_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; lean_object* v_traceState_1445_; lean_object* v_traces_1446_; lean_object* v___x_1447_; lean_object* v_traceState_1448_; lean_object* v_env_1449_; lean_object* v_nextMacroScope_1450_; lean_object* v_ngen_1451_; lean_object* v_auxDeclNGen_1452_; lean_object* v_cache_1453_; lean_object* v_recordedDeps_1454_; lean_object* v_messages_1455_; lean_object* v_infoState_1456_; lean_object* v_snapshotTasks_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1476_; 
v___x_1444_ = lean_st_ref_get(v___y_1442_);
v_traceState_1445_ = lean_ctor_get(v___x_1444_, 4);
lean_inc_ref(v_traceState_1445_);
lean_dec(v___x_1444_);
v_traces_1446_ = lean_ctor_get(v_traceState_1445_, 0);
lean_inc_ref(v_traces_1446_);
lean_dec_ref(v_traceState_1445_);
v___x_1447_ = lean_st_ref_take(v___y_1442_);
v_traceState_1448_ = lean_ctor_get(v___x_1447_, 4);
v_env_1449_ = lean_ctor_get(v___x_1447_, 0);
v_nextMacroScope_1450_ = lean_ctor_get(v___x_1447_, 1);
v_ngen_1451_ = lean_ctor_get(v___x_1447_, 2);
v_auxDeclNGen_1452_ = lean_ctor_get(v___x_1447_, 3);
v_cache_1453_ = lean_ctor_get(v___x_1447_, 5);
v_recordedDeps_1454_ = lean_ctor_get(v___x_1447_, 6);
v_messages_1455_ = lean_ctor_get(v___x_1447_, 7);
v_infoState_1456_ = lean_ctor_get(v___x_1447_, 8);
v_snapshotTasks_1457_ = lean_ctor_get(v___x_1447_, 9);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1459_ = v___x_1447_;
v_isShared_1460_ = v_isSharedCheck_1476_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_snapshotTasks_1457_);
lean_inc(v_infoState_1456_);
lean_inc(v_messages_1455_);
lean_inc(v_recordedDeps_1454_);
lean_inc(v_cache_1453_);
lean_inc(v_traceState_1448_);
lean_inc(v_auxDeclNGen_1452_);
lean_inc(v_ngen_1451_);
lean_inc(v_nextMacroScope_1450_);
lean_inc(v_env_1449_);
lean_dec(v___x_1447_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1476_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
uint64_t v_tid_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1474_; 
v_tid_1461_ = lean_ctor_get_uint64(v_traceState_1448_, sizeof(void*)*1);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_traceState_1448_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; 
v_unused_1475_ = lean_ctor_get(v_traceState_1448_, 0);
lean_dec(v_unused_1475_);
v___x_1463_ = v_traceState_1448_;
v_isShared_1464_ = v_isSharedCheck_1474_;
goto v_resetjp_1462_;
}
else
{
lean_dec(v_traceState_1448_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1474_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v___x_1465_);
lean_ctor_set_uint64(v_reuseFailAlloc_1473_, sizeof(void*)*1, v_tid_1461_);
v___x_1467_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
lean_object* v___x_1469_; 
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v___x_1467_);
v___x_1469_ = v___x_1459_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_env_1449_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_nextMacroScope_1450_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_ngen_1451_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_auxDeclNGen_1452_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v_cache_1453_);
lean_ctor_set(v_reuseFailAlloc_1472_, 6, v_recordedDeps_1454_);
lean_ctor_set(v_reuseFailAlloc_1472_, 7, v_messages_1455_);
lean_ctor_set(v_reuseFailAlloc_1472_, 8, v_infoState_1456_);
lean_ctor_set(v_reuseFailAlloc_1472_, 9, v_snapshotTasks_1457_);
v___x_1469_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_st_ref_put(v___y_1442_, v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_traces_1446_);
return v___x_1471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1477_);
lean_dec(v___y_1477_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1483_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
return v_res_1491_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1492_, lean_object* v_opt_1493_){
_start:
{
lean_object* v_name_1494_; lean_object* v_defValue_1495_; lean_object* v_map_1496_; lean_object* v___x_1497_; 
v_name_1494_ = lean_ctor_get(v_opt_1493_, 0);
v_defValue_1495_ = lean_ctor_get(v_opt_1493_, 1);
v_map_1496_ = lean_ctor_get(v_opts_1492_, 0);
v___x_1497_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1496_, v_name_1494_);
if (lean_obj_tag(v___x_1497_) == 0)
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_unbox(v_defValue_1495_);
return v___x_1498_;
}
else
{
lean_object* v_val_1499_; 
v_val_1499_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v___x_1497_, 1);
if (lean_obj_tag(v_val_1499_) == 1)
{
uint8_t v_v_1500_; 
v_v_1500_ = lean_ctor_get_uint8(v_val_1499_, 0);
lean_dec_ref_known(v_val_1499_, 0);
return v_v_1500_;
}
else
{
uint8_t v___x_1501_; 
lean_dec(v_val_1499_);
v___x_1501_ = lean_unbox(v_defValue_1495_);
return v___x_1501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1502_, lean_object* v_opt_1503_){
_start:
{
uint8_t v_res_1504_; lean_object* v_r_1505_; 
v_res_1504_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1502_, v_opt_1503_);
lean_dec_ref(v_opt_1503_);
lean_dec_ref(v_opts_1502_);
v_r_1505_ = lean_box(v_res_1504_);
return v_r_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1506_, lean_object* v_fnIndex_1507_, lean_object* v_recArg_1508_, lean_object* v_below_1509_, lean_object* v_Cs_1510_, lean_object* v_belowDict_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_array_get_borrowed(v___x_1506_, v_Cs_1510_, v_fnIndex_1507_);
lean_inc(v___x_1517_);
v___x_1518_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1517_, v_belowDict_1511_, v_recArg_1508_, v_below_1509_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1519_, lean_object* v_fnIndex_1520_, lean_object* v_recArg_1521_, lean_object* v_below_1522_, lean_object* v_Cs_1523_, lean_object* v_belowDict_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1519_, v_fnIndex_1520_, v_recArg_1521_, v_below_1522_, v_Cs_1523_, v_belowDict_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec_ref(v_Cs_1523_);
lean_dec(v_fnIndex_1520_);
lean_dec_ref(v___x_1519_);
return v_res_1530_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1537_, lean_object* v_recArg_1538_, lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; 
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
v___x_1545_ = lean_infer_type(v_below_1537_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1560_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1560_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1550_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1551_ = l_Lean_MessageData_ofExpr(v_recArg_1538_);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = l_Lean_MessageData_ofExpr(v_a_1546_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1556_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec_ref(v_recArg_1538_);
v_a_1561_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1545_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1545_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1569_, lean_object* v_recArg_1570_, lean_object* v_x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1569_, v_recArg_1570_, v_x_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec_ref(v_x_1571_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1578_, size_t v_i_1579_, lean_object* v_bs_1580_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = lean_usize_dec_lt(v_i_1579_, v_sz_1578_);
if (v___x_1581_ == 0)
{
return v_bs_1580_;
}
else
{
lean_object* v_v_1582_; lean_object* v_msg_1583_; lean_object* v___x_1584_; lean_object* v_bs_x27_1585_; size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v_v_1582_ = lean_array_uget_borrowed(v_bs_1580_, v_i_1579_);
v_msg_1583_ = lean_ctor_get(v_v_1582_, 1);
lean_inc_ref(v_msg_1583_);
v___x_1584_ = lean_unsigned_to_nat(0u);
v_bs_x27_1585_ = lean_array_uset(v_bs_1580_, v_i_1579_, v___x_1584_);
v___x_1586_ = ((size_t)1ULL);
v___x_1587_ = lean_usize_add(v_i_1579_, v___x_1586_);
v___x_1588_ = lean_array_uset(v_bs_x27_1585_, v_i_1579_, v_msg_1583_);
v_i_1579_ = v___x_1587_;
v_bs_1580_ = v___x_1588_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1590_, lean_object* v_i_1591_, lean_object* v_bs_1592_){
_start:
{
size_t v_sz_boxed_1593_; size_t v_i_boxed_1594_; lean_object* v_res_1595_; 
v_sz_boxed_1593_ = lean_unbox_usize(v_sz_1590_);
lean_dec(v_sz_1590_);
v_i_boxed_1594_ = lean_unbox_usize(v_i_1591_);
lean_dec(v_i_1591_);
v_res_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_boxed_1593_, v_i_boxed_1594_, v_bs_1592_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1596_, lean_object* v_data_1597_, lean_object* v_ref_1598_, lean_object* v_msg_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_toCold_1605_; lean_object* v_currRecDepth_1606_; lean_object* v_ref_1607_; uint16_t v_optionFlags_1608_; uint8_t v_suppressElabErrors_1609_; uint8_t v_checkDeprecated_1610_; uint8_t v_isRecordingDeps_1611_; lean_object* v_ref_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v_traceState_1615_; lean_object* v_traces_1616_; lean_object* v___x_1617_; size_t v_sz_1618_; size_t v___x_1619_; lean_object* v___x_1620_; lean_object* v_msg_1621_; lean_object* v___x_1622_; lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1661_; 
v_toCold_1605_ = lean_ctor_get(v___y_1602_, 0);
v_currRecDepth_1606_ = lean_ctor_get(v___y_1602_, 1);
v_ref_1607_ = lean_ctor_get(v___y_1602_, 2);
v_optionFlags_1608_ = lean_ctor_get_uint16(v___y_1602_, sizeof(void*)*3);
v_suppressElabErrors_1609_ = lean_ctor_get_uint8(v___y_1602_, sizeof(void*)*3 + 2);
v_checkDeprecated_1610_ = lean_ctor_get_uint8(v___y_1602_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1611_ = lean_ctor_get_uint8(v___y_1602_, sizeof(void*)*3 + 4);
v_ref_1612_ = l_Lean_replaceRef(v_ref_1598_, v_ref_1607_);
lean_inc(v_currRecDepth_1606_);
lean_inc_ref(v_toCold_1605_);
v___x_1613_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1613_, 0, v_toCold_1605_);
lean_ctor_set(v___x_1613_, 1, v_currRecDepth_1606_);
lean_ctor_set(v___x_1613_, 2, v_ref_1612_);
lean_ctor_set_uint16(v___x_1613_, sizeof(void*)*3, v_optionFlags_1608_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 2, v_suppressElabErrors_1609_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 3, v_checkDeprecated_1610_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 4, v_isRecordingDeps_1611_);
v___x_1614_ = lean_st_ref_get(v___y_1603_);
v_traceState_1615_ = lean_ctor_get(v___x_1614_, 4);
lean_inc_ref(v_traceState_1615_);
lean_dec(v___x_1614_);
v_traces_1616_ = lean_ctor_get(v_traceState_1615_, 0);
lean_inc_ref(v_traces_1616_);
lean_dec_ref(v_traceState_1615_);
v___x_1617_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1616_);
lean_dec_ref(v_traces_1616_);
v_sz_1618_ = lean_array_size(v___x_1617_);
v___x_1619_ = ((size_t)0ULL);
v___x_1620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1618_, v___x_1619_, v___x_1617_);
v_msg_1621_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1621_, 0, v_data_1597_);
lean_ctor_set(v_msg_1621_, 1, v_msg_1599_);
lean_ctor_set(v_msg_1621_, 2, v___x_1620_);
v___x_1622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1621_, v___y_1600_, v___y_1601_, v___x_1613_, v___y_1603_);
lean_dec_ref_known(v___x_1613_, 3);
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1661_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1661_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v_traceState_1628_; lean_object* v_env_1629_; lean_object* v_nextMacroScope_1630_; lean_object* v_ngen_1631_; lean_object* v_auxDeclNGen_1632_; lean_object* v_cache_1633_; lean_object* v_recordedDeps_1634_; lean_object* v_messages_1635_; lean_object* v_infoState_1636_; lean_object* v_snapshotTasks_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1660_; 
v___x_1627_ = lean_st_ref_take(v___y_1603_);
v_traceState_1628_ = lean_ctor_get(v___x_1627_, 4);
v_env_1629_ = lean_ctor_get(v___x_1627_, 0);
v_nextMacroScope_1630_ = lean_ctor_get(v___x_1627_, 1);
v_ngen_1631_ = lean_ctor_get(v___x_1627_, 2);
v_auxDeclNGen_1632_ = lean_ctor_get(v___x_1627_, 3);
v_cache_1633_ = lean_ctor_get(v___x_1627_, 5);
v_recordedDeps_1634_ = lean_ctor_get(v___x_1627_, 6);
v_messages_1635_ = lean_ctor_get(v___x_1627_, 7);
v_infoState_1636_ = lean_ctor_get(v___x_1627_, 8);
v_snapshotTasks_1637_ = lean_ctor_get(v___x_1627_, 9);
v_isSharedCheck_1660_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1660_ == 0)
{
v___x_1639_ = v___x_1627_;
v_isShared_1640_ = v_isSharedCheck_1660_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_snapshotTasks_1637_);
lean_inc(v_infoState_1636_);
lean_inc(v_messages_1635_);
lean_inc(v_recordedDeps_1634_);
lean_inc(v_cache_1633_);
lean_inc(v_traceState_1628_);
lean_inc(v_auxDeclNGen_1632_);
lean_inc(v_ngen_1631_);
lean_inc(v_nextMacroScope_1630_);
lean_inc(v_env_1629_);
lean_dec(v___x_1627_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1660_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
uint64_t v_tid_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1658_; 
v_tid_1641_ = lean_ctor_get_uint64(v_traceState_1628_, sizeof(void*)*1);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_traceState_1628_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v_traceState_1628_, 0);
lean_dec(v_unused_1659_);
v___x_1643_ = v_traceState_1628_;
v_isShared_1644_ = v_isSharedCheck_1658_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v_traceState_1628_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1658_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_ref_1598_);
lean_ctor_set(v___x_1646_, 1, v_a_1623_);
v___x_1647_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1596_, v___x_1646_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1647_);
v___x_1649_ = v___x_1643_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1647_);
lean_ctor_set_uint64(v_reuseFailAlloc_1657_, sizeof(void*)*1, v_tid_1641_);
v___x_1649_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 4, v___x_1649_);
v___x_1651_ = v___x_1639_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_env_1629_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_nextMacroScope_1630_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_ngen_1631_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_auxDeclNGen_1632_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1656_, 5, v_cache_1633_);
lean_ctor_set(v_reuseFailAlloc_1656_, 6, v_recordedDeps_1634_);
lean_ctor_set(v_reuseFailAlloc_1656_, 7, v_messages_1635_);
lean_ctor_set(v_reuseFailAlloc_1656_, 8, v_infoState_1636_);
lean_ctor_set(v_reuseFailAlloc_1656_, 9, v_snapshotTasks_1637_);
v___x_1651_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_st_ref_put(v___y_1603_, v___x_1651_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1645_);
v___x_1654_ = v___x_1625_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1645_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1662_, lean_object* v_data_1663_, lean_object* v_ref_1664_, lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1662_, v_data_1663_, v_ref_1664_, v_msg_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1672_, lean_object* v_opt_1673_){
_start:
{
lean_object* v_name_1674_; lean_object* v_defValue_1675_; lean_object* v_map_1676_; lean_object* v___x_1677_; 
v_name_1674_ = lean_ctor_get(v_opt_1673_, 0);
v_defValue_1675_ = lean_ctor_get(v_opt_1673_, 1);
v_map_1676_ = lean_ctor_get(v_opts_1672_, 0);
v___x_1677_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1676_, v_name_1674_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_inc(v_defValue_1675_);
return v_defValue_1675_;
}
else
{
lean_object* v_val_1678_; 
v_val_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_val_1678_);
lean_dec_ref_known(v___x_1677_, 1);
if (lean_obj_tag(v_val_1678_) == 3)
{
lean_object* v_v_1679_; 
v_v_1679_ = lean_ctor_get(v_val_1678_, 0);
lean_inc(v_v_1679_);
lean_dec_ref_known(v_val_1678_, 1);
return v_v_1679_;
}
else
{
lean_dec(v_val_1678_);
lean_inc(v_defValue_1675_);
return v_defValue_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1680_, lean_object* v_opt_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1680_, v_opt_1681_);
lean_dec_ref(v_opt_1681_);
lean_dec_ref(v_opts_1680_);
return v_res_1682_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1683_){
_start:
{
if (lean_obj_tag(v_e_1683_) == 0)
{
uint8_t v___x_1684_; 
v___x_1684_ = 2;
return v___x_1684_;
}
else
{
lean_object* v_a_1685_; uint8_t v___x_1686_; 
v_a_1685_ = lean_ctor_get(v_e_1683_, 0);
v___x_1686_ = l_Lean_Expr_hasSyntheticSorry(v_a_1685_);
if (v___x_1686_ == 0)
{
uint8_t v___x_1687_; 
v___x_1687_ = 0;
return v___x_1687_;
}
else
{
uint8_t v___x_1688_; 
v___x_1688_ = 1;
return v___x_1688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1689_){
_start:
{
uint8_t v_res_1690_; lean_object* v_r_1691_; 
v_res_1690_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1689_);
lean_dec_ref(v_e_1689_);
v_r_1691_ = lean_box(v_res_1690_);
return v_r_1691_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1692_){
_start:
{
if (lean_obj_tag(v_x_1692_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
v_a_1694_ = lean_ctor_get(v_x_1692_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1692_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v_x_1692_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v_x_1692_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set_tag(v___x_1696_, 1);
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v_x_1692_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v_x_1692_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v_x_1692_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v_x_1692_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 0);
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1710_);
return v_res_1712_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1715_ = l_Lean_stringToMessageData(v___x_1714_);
return v___x_1715_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1716_; double v___x_1717_; 
v___x_1716_ = lean_unsigned_to_nat(1000u);
v___x_1717_ = lean_float_of_nat(v___x_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1718_, uint8_t v_collapsed_1719_, lean_object* v_tag_1720_, lean_object* v_opts_1721_, uint8_t v_clsEnabled_1722_, lean_object* v_oldTraces_1723_, lean_object* v_msg_1724_, lean_object* v_resStartStop_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_fst_1731_; lean_object* v_snd_1732_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v_data_1736_; lean_object* v_fst_1747_; lean_object* v_snd_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___y_1752_; lean_object* v_a_1753_; uint8_t v___y_1768_; double v___y_1800_; 
v_fst_1731_ = lean_ctor_get(v_resStartStop_1725_, 0);
lean_inc(v_fst_1731_);
v_snd_1732_ = lean_ctor_get(v_resStartStop_1725_, 1);
lean_inc(v_snd_1732_);
lean_dec_ref(v_resStartStop_1725_);
v_fst_1747_ = lean_ctor_get(v_snd_1732_, 0);
lean_inc(v_fst_1747_);
v_snd_1748_ = lean_ctor_get(v_snd_1732_, 1);
lean_inc(v_snd_1748_);
lean_dec(v_snd_1732_);
v___x_1749_ = l_Lean_trace_profiler;
v___x_1750_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1721_, v___x_1749_);
if (v___x_1750_ == 0)
{
v___y_1768_ = v___x_1750_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1806_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1721_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; double v___x_1809_; double v___x_1810_; double v___x_1811_; 
v___x_1807_ = l_Lean_trace_profiler_threshold;
v___x_1808_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1721_, v___x_1807_);
v___x_1809_ = lean_float_of_nat(v___x_1808_);
v___x_1810_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2);
v___x_1811_ = lean_float_div(v___x_1809_, v___x_1810_);
v___y_1800_ = v___x_1811_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1813_; double v___x_1814_; 
v___x_1812_ = l_Lean_trace_profiler_threshold;
v___x_1813_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1721_, v___x_1812_);
v___x_1814_ = lean_float_of_nat(v___x_1813_);
v___y_1800_ = v___x_1814_;
goto v___jp_1799_;
}
}
v___jp_1733_:
{
lean_object* v___x_1737_; 
lean_inc(v___y_1734_);
v___x_1737_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1723_, v_data_1736_, v___y_1734_, v___y_1735_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref_known(v___x_1737_, 1);
v___x_1738_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1731_);
return v___x_1738_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_fst_1731_);
v_a_1739_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1737_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
v___jp_1751_:
{
uint8_t v_result_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; double v___x_1757_; lean_object* v_data_1758_; 
v_result_1754_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1731_);
v___x_1755_ = lean_box(v_result_1754_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
v___x_1757_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1720_);
lean_inc_ref(v___x_1756_);
lean_inc(v_cls_1718_);
v_data_1758_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1758_, 0, v_cls_1718_);
lean_ctor_set(v_data_1758_, 1, v___x_1756_);
lean_ctor_set(v_data_1758_, 2, v_tag_1720_);
lean_ctor_set_float(v_data_1758_, sizeof(void*)*3, v___x_1757_);
lean_ctor_set_float(v_data_1758_, sizeof(void*)*3 + 8, v___x_1757_);
lean_ctor_set_uint8(v_data_1758_, sizeof(void*)*3 + 16, v_collapsed_1719_);
if (v___x_1750_ == 0)
{
lean_dec_ref_known(v___x_1756_, 1);
lean_dec(v_snd_1748_);
lean_dec(v_fst_1747_);
lean_dec_ref(v_tag_1720_);
lean_dec(v_cls_1718_);
v___y_1734_ = v___y_1752_;
v___y_1735_ = v_a_1753_;
v_data_1736_ = v_data_1758_;
goto v___jp_1733_;
}
else
{
lean_object* v_data_1759_; double v___x_1760_; double v___x_1761_; 
lean_dec_ref_known(v_data_1758_, 3);
v_data_1759_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1759_, 0, v_cls_1718_);
lean_ctor_set(v_data_1759_, 1, v___x_1756_);
lean_ctor_set(v_data_1759_, 2, v_tag_1720_);
v___x_1760_ = lean_unbox_float(v_fst_1747_);
lean_dec(v_fst_1747_);
lean_ctor_set_float(v_data_1759_, sizeof(void*)*3, v___x_1760_);
v___x_1761_ = lean_unbox_float(v_snd_1748_);
lean_dec(v_snd_1748_);
lean_ctor_set_float(v_data_1759_, sizeof(void*)*3 + 8, v___x_1761_);
lean_ctor_set_uint8(v_data_1759_, sizeof(void*)*3 + 16, v_collapsed_1719_);
v___y_1734_ = v___y_1752_;
v___y_1735_ = v_a_1753_;
v_data_1736_ = v_data_1759_;
goto v___jp_1733_;
}
}
v___jp_1762_:
{
lean_object* v_ref_1763_; lean_object* v___x_1764_; 
v_ref_1763_ = lean_ctor_get(v___y_1728_, 2);
lean_inc(v___y_1729_);
lean_inc_ref(v___y_1728_);
lean_inc(v___y_1727_);
lean_inc_ref(v___y_1726_);
lean_inc(v_fst_1731_);
v___x_1764_ = lean_apply_6(v_msg_1724_, v_fst_1731_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, lean_box(0));
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___y_1752_ = v_ref_1763_;
v_a_1753_ = v_a_1765_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1766_; 
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1752_ = v_ref_1763_;
v_a_1753_ = v___x_1766_;
goto v___jp_1751_;
}
}
v___jp_1767_:
{
if (v_clsEnabled_1722_ == 0)
{
if (v___y_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v_traceState_1770_; lean_object* v_env_1771_; lean_object* v_nextMacroScope_1772_; lean_object* v_ngen_1773_; lean_object* v_auxDeclNGen_1774_; lean_object* v_cache_1775_; lean_object* v_recordedDeps_1776_; lean_object* v_messages_1777_; lean_object* v_infoState_1778_; lean_object* v_snapshotTasks_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v_snd_1748_);
lean_dec(v_fst_1747_);
lean_dec_ref(v_msg_1724_);
lean_dec_ref(v_tag_1720_);
lean_dec(v_cls_1718_);
v___x_1769_ = lean_st_ref_take(v___y_1729_);
v_traceState_1770_ = lean_ctor_get(v___x_1769_, 4);
v_env_1771_ = lean_ctor_get(v___x_1769_, 0);
v_nextMacroScope_1772_ = lean_ctor_get(v___x_1769_, 1);
v_ngen_1773_ = lean_ctor_get(v___x_1769_, 2);
v_auxDeclNGen_1774_ = lean_ctor_get(v___x_1769_, 3);
v_cache_1775_ = lean_ctor_get(v___x_1769_, 5);
v_recordedDeps_1776_ = lean_ctor_get(v___x_1769_, 6);
v_messages_1777_ = lean_ctor_get(v___x_1769_, 7);
v_infoState_1778_ = lean_ctor_get(v___x_1769_, 8);
v_snapshotTasks_1779_ = lean_ctor_get(v___x_1769_, 9);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1781_ = v___x_1769_;
v_isShared_1782_ = v_isSharedCheck_1798_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_snapshotTasks_1779_);
lean_inc(v_infoState_1778_);
lean_inc(v_messages_1777_);
lean_inc(v_recordedDeps_1776_);
lean_inc(v_cache_1775_);
lean_inc(v_traceState_1770_);
lean_inc(v_auxDeclNGen_1774_);
lean_inc(v_ngen_1773_);
lean_inc(v_nextMacroScope_1772_);
lean_inc(v_env_1771_);
lean_dec(v___x_1769_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1798_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
uint64_t v_tid_1783_; lean_object* v_traces_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1797_; 
v_tid_1783_ = lean_ctor_get_uint64(v_traceState_1770_, sizeof(void*)*1);
v_traces_1784_ = lean_ctor_get(v_traceState_1770_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_traceState_1770_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1786_ = v_traceState_1770_;
v_isShared_1787_ = v_isSharedCheck_1797_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_traces_1784_);
lean_dec(v_traceState_1770_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1797_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1723_, v_traces_1784_);
lean_dec_ref(v_traces_1784_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1788_);
v___x_1790_ = v___x_1786_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1788_);
lean_ctor_set_uint64(v_reuseFailAlloc_1796_, sizeof(void*)*1, v_tid_1783_);
v___x_1790_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
lean_object* v___x_1792_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 4, v___x_1790_);
v___x_1792_ = v___x_1781_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_env_1771_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_nextMacroScope_1772_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_ngen_1773_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_auxDeclNGen_1774_);
lean_ctor_set(v_reuseFailAlloc_1795_, 4, v___x_1790_);
lean_ctor_set(v_reuseFailAlloc_1795_, 5, v_cache_1775_);
lean_ctor_set(v_reuseFailAlloc_1795_, 6, v_recordedDeps_1776_);
lean_ctor_set(v_reuseFailAlloc_1795_, 7, v_messages_1777_);
lean_ctor_set(v_reuseFailAlloc_1795_, 8, v_infoState_1778_);
lean_ctor_set(v_reuseFailAlloc_1795_, 9, v_snapshotTasks_1779_);
v___x_1792_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_st_ref_put(v___y_1729_, v___x_1792_);
v___x_1794_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1731_);
return v___x_1794_;
}
}
}
}
}
else
{
goto v___jp_1762_;
}
}
else
{
goto v___jp_1762_;
}
}
v___jp_1799_:
{
double v___x_1801_; double v___x_1802_; double v___x_1803_; uint8_t v___x_1804_; 
v___x_1801_ = lean_unbox_float(v_snd_1748_);
v___x_1802_ = lean_unbox_float(v_fst_1747_);
v___x_1803_ = lean_float_sub(v___x_1801_, v___x_1802_);
v___x_1804_ = lean_float_decLt(v___y_1800_, v___x_1803_);
v___y_1768_ = v___x_1804_;
goto v___jp_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1815_, lean_object* v_collapsed_1816_, lean_object* v_tag_1817_, lean_object* v_opts_1818_, lean_object* v_clsEnabled_1819_, lean_object* v_oldTraces_1820_, lean_object* v_msg_1821_, lean_object* v_resStartStop_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
uint8_t v_collapsed_boxed_1828_; uint8_t v_clsEnabled_boxed_1829_; lean_object* v_res_1830_; 
v_collapsed_boxed_1828_ = lean_unbox(v_collapsed_1816_);
v_clsEnabled_boxed_1829_ = lean_unbox(v_clsEnabled_1819_);
v_res_1830_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1815_, v_collapsed_boxed_1828_, v_tag_1817_, v_opts_1818_, v_clsEnabled_boxed_1829_, v_oldTraces_1820_, v_msg_1821_, v_resStartStop_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_);
lean_dec(v___y_1826_);
lean_dec_ref(v___y_1825_);
lean_dec(v___y_1824_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v_opts_1818_);
return v_res_1830_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1831_; double v___x_1832_; 
v___x_1831_ = lean_unsigned_to_nat(1000000000u);
v___x_1832_ = lean_float_of_nat(v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1833_, lean_object* v_numIndParams_1834_, lean_object* v_positions_1835_, lean_object* v_fnIndex_1836_, lean_object* v_recArg_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_toCold_1843_; lean_object* v_options_1844_; lean_object* v_inheritedTraceOptions_1845_; uint8_t v_hasTrace_1846_; lean_object* v___x_1847_; lean_object* v___f_1848_; 
v_toCold_1843_ = lean_ctor_get(v_a_1840_, 0);
v_options_1844_ = lean_ctor_get(v_toCold_1843_, 2);
v_inheritedTraceOptions_1845_ = lean_ctor_get(v_toCold_1843_, 11);
v_hasTrace_1846_ = lean_ctor_get_uint8(v_options_1844_, sizeof(void*)*1);
v___x_1847_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1833_);
lean_inc_ref(v_recArg_1837_);
v___f_1848_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1848_, 0, v___x_1847_);
lean_closure_set(v___f_1848_, 1, v_fnIndex_1836_);
lean_closure_set(v___f_1848_, 2, v_recArg_1837_);
lean_closure_set(v___f_1848_, 3, v_below_1833_);
if (v_hasTrace_1846_ == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref(v_recArg_1837_);
v___x_1849_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1833_, v_numIndParams_1834_, v_positions_1835_, v___f_1848_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1849_;
}
else
{
lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v_a_1858_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v_a_1873_; 
lean_inc_ref(v_below_1833_);
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1850_, 0, v_below_1833_);
lean_closure_set(v___f_1850_, 1, v_recArg_1837_);
v___x_1851_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1852_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1853_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1854_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1845_, v_options_1844_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1923_; uint8_t v___x_1924_; 
v___x_1923_ = l_Lean_trace_profiler;
v___x_1924_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1844_, v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec_ref(v___f_1850_);
v___x_1925_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1833_, v_numIndParams_1834_, v_positions_1835_, v___f_1848_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1925_;
}
else
{
goto v___jp_1882_;
}
}
else
{
goto v___jp_1882_;
}
v___jp_1855_:
{
lean_object* v___x_1859_; double v___x_1860_; double v___x_1861_; double v___x_1862_; double v___x_1863_; double v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1859_ = lean_io_mono_nanos_now();
v___x_1860_ = lean_float_of_nat(v___y_1856_);
v___x_1861_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1862_ = lean_float_div(v___x_1860_, v___x_1861_);
v___x_1863_ = lean_float_of_nat(v___x_1859_);
v___x_1864_ = lean_float_div(v___x_1863_, v___x_1861_);
v___x_1865_ = lean_box_float(v___x_1862_);
v___x_1866_ = lean_box_float(v___x_1864_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v_a_1858_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1851_, v_hasTrace_1846_, v___x_1852_, v_options_1844_, v___x_1854_, v___y_1857_, v___f_1850_, v___x_1868_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1869_;
}
v___jp_1870_:
{
lean_object* v___x_1874_; double v___x_1875_; double v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1874_ = lean_io_get_num_heartbeats();
v___x_1875_ = lean_float_of_nat(v___y_1871_);
v___x_1876_ = lean_float_of_nat(v___x_1874_);
v___x_1877_ = lean_box_float(v___x_1875_);
v___x_1878_ = lean_box_float(v___x_1876_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v_a_1873_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1851_, v_hasTrace_1846_, v___x_1852_, v_options_1844_, v___x_1854_, v___y_1872_, v___f_1850_, v___x_1880_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
return v___x_1881_;
}
v___jp_1882_:
{
lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v___x_1883_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1841_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1886_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1844_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_io_mono_nanos_now();
v___x_1888_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1833_, v_numIndParams_1834_, v_positions_1835_, v___f_1848_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1888_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1888_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 1);
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
v___y_1856_ = v___x_1887_;
v___y_1857_ = v_a_1884_;
v_a_1858_ = v___x_1894_;
goto v___jp_1855_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
v_a_1897_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1888_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1888_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 0);
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
v___y_1856_ = v___x_1887_;
v___y_1857_ = v_a_1884_;
v_a_1858_ = v___x_1902_;
goto v___jp_1855_;
}
}
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_io_get_num_heartbeats();
v___x_1906_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1833_, v_numIndParams_1834_, v_positions_1835_, v___f_1848_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set_tag(v___x_1909_, 1);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
v___y_1871_ = v___x_1905_;
v___y_1872_ = v_a_1884_;
v_a_1873_ = v___x_1912_;
goto v___jp_1870_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1906_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1906_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set_tag(v___x_1917_, 0);
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v___y_1871_ = v___x_1905_;
v___y_1872_ = v_a_1884_;
v_a_1873_ = v___x_1920_;
goto v___jp_1870_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1926_, lean_object* v_numIndParams_1927_, lean_object* v_positions_1928_, lean_object* v_fnIndex_1929_, lean_object* v_recArg_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Elab_Structural_toBelow(v_below_1926_, v_numIndParams_1927_, v_positions_1928_, v_fnIndex_1929_, v_recArg_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
lean_dec(v_a_1934_);
lean_dec_ref(v_a_1933_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1937_, lean_object* v_x_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1938_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1945_, lean_object* v_x_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1945_, v_x_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1953_, lean_object* v___y_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v___x_1961_; 
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v___y_1954_);
v___x_1961_ = lean_apply_7(v_k_1953_, v_b_1955_, v___y_1954_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, lean_box(0));
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_1962_, lean_object* v___y_1963_, lean_object* v_b_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1962_, v___y_1963_, v_b_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1963_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_1971_, uint8_t v_bi_1972_, lean_object* v_type_1973_, lean_object* v_k_1974_, uint8_t v_kind_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___f_1982_; lean_object* v___x_1983_; 
lean_inc(v___y_1976_);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1982_, 0, v_k_1974_);
lean_closure_set(v___f_1982_, 1, v___y_1976_);
v___x_1983_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1971_, v_bi_1972_, v_type_1973_, v___f_1982_, v_kind_1975_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1983_) == 0)
{
return v___x_1983_;
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_1992_, lean_object* v_bi_1993_, lean_object* v_type_1994_, lean_object* v_k_1995_, lean_object* v_kind_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v_bi_boxed_2003_; uint8_t v_kind_boxed_2004_; lean_object* v_res_2005_; 
v_bi_boxed_2003_ = lean_unbox(v_bi_1993_);
v_kind_boxed_2004_ = lean_unbox(v_kind_1996_);
v_res_2005_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_1992_, v_bi_boxed_2003_, v_type_1994_, v_k_1995_, v_kind_boxed_2004_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2006_, lean_object* v_name_2007_, uint8_t v_bi_2008_, lean_object* v_type_2009_, lean_object* v_k_2010_, uint8_t v_kind_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2007_, v_bi_2008_, v_type_2009_, v_k_2010_, v_kind_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2019_, lean_object* v_name_2020_, lean_object* v_bi_2021_, lean_object* v_type_2022_, lean_object* v_k_2023_, lean_object* v_kind_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
uint8_t v_bi_boxed_2031_; uint8_t v_kind_boxed_2032_; lean_object* v_res_2033_; 
v_bi_boxed_2031_ = lean_unbox(v_bi_2021_);
v_kind_boxed_2032_ = lean_unbox(v_kind_2024_);
v_res_2033_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2019_, v_name_2020_, v_bi_boxed_2031_, v_type_2022_, v_k_2023_, v_kind_boxed_2032_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2034_, lean_object* v___y_2035_, lean_object* v_b_2036_, lean_object* v_c_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v___x_2043_; 
lean_inc(v___y_2041_);
lean_inc_ref(v___y_2040_);
lean_inc(v___y_2039_);
lean_inc_ref(v___y_2038_);
lean_inc(v___y_2035_);
v___x_2043_ = lean_apply_8(v_k_2034_, v_b_2036_, v_c_2037_, v___y_2035_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, lean_box(0));
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2044_, lean_object* v___y_2045_, lean_object* v_b_2046_, lean_object* v_c_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2044_, v___y_2045_, v_b_2046_, v_c_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2045_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2054_, lean_object* v_maxFVars_2055_, lean_object* v_k_2056_, uint8_t v_cleanupAnnotations_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v___f_2064_; uint8_t v___x_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_inc(v___y_2058_);
v___f_2064_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2064_, 0, v_k_2056_);
lean_closure_set(v___f_2064_, 1, v___y_2058_);
v___x_2065_ = 1;
v___x_2066_ = 0;
v___x_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2067_, 0, v_maxFVars_2055_);
v___x_2068_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2054_, v___x_2065_, v___x_2066_, v___x_2065_, v___x_2066_, v___x_2067_, v___f_2064_, v_cleanupAnnotations_2057_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec_ref_known(v___x_2067_, 1);
if (lean_obj_tag(v___x_2068_) == 0)
{
return v___x_2068_;
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2077_, lean_object* v_maxFVars_2078_, lean_object* v_k_2079_, lean_object* v_cleanupAnnotations_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2087_; lean_object* v_res_2088_; 
v_cleanupAnnotations_boxed_2087_ = lean_unbox(v_cleanupAnnotations_2080_);
v_res_2088_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2077_, v_maxFVars_2078_, v_k_2079_, v_cleanupAnnotations_boxed_2087_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2089_, lean_object* v_e_2090_, lean_object* v_maxFVars_2091_, lean_object* v_k_2092_, uint8_t v_cleanupAnnotations_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v___x_2100_; 
v___x_2100_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2090_, v_maxFVars_2091_, v_k_2092_, v_cleanupAnnotations_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2101_, lean_object* v_e_2102_, lean_object* v_maxFVars_2103_, lean_object* v_k_2104_, lean_object* v_cleanupAnnotations_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2112_; lean_object* v_res_2113_; 
v_cleanupAnnotations_boxed_2112_ = lean_unbox(v_cleanupAnnotations_2105_);
v_res_2113_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2101_, v_e_2102_, v_maxFVars_2103_, v_k_2104_, v_cleanupAnnotations_boxed_2112_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2114_, lean_object* v_msg_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_ref_2121_; lean_object* v___x_2122_; lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2168_; 
v_ref_2121_ = lean_ctor_get(v___y_2118_, 2);
v___x_2122_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2168_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2168_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v_traceState_2128_; lean_object* v_env_2129_; lean_object* v_nextMacroScope_2130_; lean_object* v_ngen_2131_; lean_object* v_auxDeclNGen_2132_; lean_object* v_cache_2133_; lean_object* v_recordedDeps_2134_; lean_object* v_messages_2135_; lean_object* v_infoState_2136_; lean_object* v_snapshotTasks_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2167_; 
v___x_2127_ = lean_st_ref_take(v___y_2119_);
v_traceState_2128_ = lean_ctor_get(v___x_2127_, 4);
v_env_2129_ = lean_ctor_get(v___x_2127_, 0);
v_nextMacroScope_2130_ = lean_ctor_get(v___x_2127_, 1);
v_ngen_2131_ = lean_ctor_get(v___x_2127_, 2);
v_auxDeclNGen_2132_ = lean_ctor_get(v___x_2127_, 3);
v_cache_2133_ = lean_ctor_get(v___x_2127_, 5);
v_recordedDeps_2134_ = lean_ctor_get(v___x_2127_, 6);
v_messages_2135_ = lean_ctor_get(v___x_2127_, 7);
v_infoState_2136_ = lean_ctor_get(v___x_2127_, 8);
v_snapshotTasks_2137_ = lean_ctor_get(v___x_2127_, 9);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2139_ = v___x_2127_;
v_isShared_2140_ = v_isSharedCheck_2167_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_snapshotTasks_2137_);
lean_inc(v_infoState_2136_);
lean_inc(v_messages_2135_);
lean_inc(v_recordedDeps_2134_);
lean_inc(v_cache_2133_);
lean_inc(v_traceState_2128_);
lean_inc(v_auxDeclNGen_2132_);
lean_inc(v_ngen_2131_);
lean_inc(v_nextMacroScope_2130_);
lean_inc(v_env_2129_);
lean_dec(v___x_2127_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2167_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
uint64_t v_tid_2141_; lean_object* v_traces_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2166_; 
v_tid_2141_ = lean_ctor_get_uint64(v_traceState_2128_, sizeof(void*)*1);
v_traces_2142_ = lean_ctor_get(v_traceState_2128_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_traceState_2128_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2144_ = v_traceState_2128_;
v_isShared_2145_ = v_isSharedCheck_2166_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_traces_2142_);
lean_dec(v_traceState_2128_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2166_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; double v___x_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_box(0);
v___x_2148_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2149_ = 0;
v___x_2150_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2151_, 0, v_cls_2114_);
lean_ctor_set(v___x_2151_, 1, v___x_2147_);
lean_ctor_set(v___x_2151_, 2, v___x_2150_);
lean_ctor_set_float(v___x_2151_, sizeof(void*)*3, v___x_2148_);
lean_ctor_set_float(v___x_2151_, sizeof(void*)*3 + 8, v___x_2148_);
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*3 + 16, v___x_2149_);
v___x_2152_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2153_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2151_);
lean_ctor_set(v___x_2153_, 1, v_a_2123_);
lean_ctor_set(v___x_2153_, 2, v___x_2152_);
lean_inc(v_ref_2121_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_ref_2121_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_PersistentArray_push___redArg(v_traces_2142_, v___x_2154_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 0, v___x_2155_);
v___x_2157_ = v___x_2144_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2155_);
lean_ctor_set_uint64(v_reuseFailAlloc_2165_, sizeof(void*)*1, v_tid_2141_);
v___x_2157_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v___x_2159_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 4, v___x_2157_);
v___x_2159_ = v___x_2139_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_env_2129_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_nextMacroScope_2130_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_ngen_2131_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_auxDeclNGen_2132_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2164_, 5, v_cache_2133_);
lean_ctor_set(v_reuseFailAlloc_2164_, 6, v_recordedDeps_2134_);
lean_ctor_set(v_reuseFailAlloc_2164_, 7, v_messages_2135_);
lean_ctor_set(v_reuseFailAlloc_2164_, 8, v_infoState_2136_);
lean_ctor_set(v_reuseFailAlloc_2164_, 9, v_snapshotTasks_2137_);
v___x_2159_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_st_ref_put(v___y_2119_, v___x_2159_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2146_);
v___x_2162_ = v___x_2125_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2146_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2169_, lean_object* v_msg_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2169_, v_msg_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; lean_object* v_env_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_st_ref_get(v___y_2178_);
v_env_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc_ref(v_env_2181_);
lean_dec(v___x_2180_);
v___x_2182_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2181_, v_declName_2177_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2184_, v___y_2185_);
lean_dec(v___y_2185_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v_toApplicative_2196_; lean_object* v_toFunctor_2197_; lean_object* v_toSeq_2198_; lean_object* v_toSeqLeft_2199_; lean_object* v_toSeqRight_2200_; lean_object* v___f_2201_; lean_object* v___f_2202_; lean_object* v___f_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___f_2206_; lean_object* v___f_2207_; lean_object* v___f_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_toApplicative_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2244_; 
v___x_2195_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2196_ = lean_ctor_get(v___x_2195_, 0);
v_toFunctor_2197_ = lean_ctor_get(v_toApplicative_2196_, 0);
v_toSeq_2198_ = lean_ctor_get(v_toApplicative_2196_, 2);
v_toSeqLeft_2199_ = lean_ctor_get(v_toApplicative_2196_, 3);
v_toSeqRight_2200_ = lean_ctor_get(v_toApplicative_2196_, 4);
v___f_2201_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2202_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2197_, 2);
v___f_2203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2203_, 0, v_toFunctor_2197_);
v___f_2204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2204_, 0, v_toFunctor_2197_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___f_2203_);
lean_ctor_set(v___x_2205_, 1, v___f_2204_);
lean_inc(v_toSeqRight_2200_);
v___f_2206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2206_, 0, v_toSeqRight_2200_);
lean_inc(v_toSeqLeft_2199_);
v___f_2207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2207_, 0, v_toSeqLeft_2199_);
lean_inc(v_toSeq_2198_);
v___f_2208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2208_, 0, v_toSeq_2198_);
v___x_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2205_);
lean_ctor_set(v___x_2209_, 1, v___f_2201_);
lean_ctor_set(v___x_2209_, 2, v___f_2208_);
lean_ctor_set(v___x_2209_, 3, v___f_2207_);
lean_ctor_set(v___x_2209_, 4, v___f_2206_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___f_2202_);
v___x_2211_ = l_StateRefT_x27_instMonad___redArg(v___x_2210_);
v_toApplicative_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2244_ == 0)
{
lean_object* v_unused_2245_; 
v_unused_2245_ = lean_ctor_get(v___x_2211_, 1);
lean_dec(v_unused_2245_);
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2244_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_toApplicative_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2244_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v_toFunctor_2216_; lean_object* v_toSeq_2217_; lean_object* v_toSeqLeft_2218_; lean_object* v_toSeqRight_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2242_; 
v_toFunctor_2216_ = lean_ctor_get(v_toApplicative_2212_, 0);
v_toSeq_2217_ = lean_ctor_get(v_toApplicative_2212_, 2);
v_toSeqLeft_2218_ = lean_ctor_get(v_toApplicative_2212_, 3);
v_toSeqRight_2219_ = lean_ctor_get(v_toApplicative_2212_, 4);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_toApplicative_2212_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v_toApplicative_2212_, 1);
lean_dec(v_unused_2243_);
v___x_2221_ = v_toApplicative_2212_;
v_isShared_2222_ = v_isSharedCheck_2242_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_toSeqRight_2219_);
lean_inc(v_toSeqLeft_2218_);
lean_inc(v_toSeq_2217_);
lean_inc(v_toFunctor_2216_);
lean_dec(v_toApplicative_2212_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2242_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___f_2223_; lean_object* v___f_2224_; lean_object* v___f_2225_; lean_object* v___f_2226_; lean_object* v___x_2227_; lean_object* v___f_2228_; lean_object* v___f_2229_; lean_object* v___f_2230_; lean_object* v___x_2232_; 
v___f_2223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2216_);
v___f_2225_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2225_, 0, v_toFunctor_2216_);
v___f_2226_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2226_, 0, v_toFunctor_2216_);
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___f_2225_);
lean_ctor_set(v___x_2227_, 1, v___f_2226_);
v___f_2228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2228_, 0, v_toSeqRight_2219_);
v___f_2229_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2229_, 0, v_toSeqLeft_2218_);
v___f_2230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2230_, 0, v_toSeq_2217_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 4, v___f_2228_);
lean_ctor_set(v___x_2221_, 3, v___f_2229_);
lean_ctor_set(v___x_2221_, 2, v___f_2230_);
lean_ctor_set(v___x_2221_, 1, v___f_2223_);
lean_ctor_set(v___x_2221_, 0, v___x_2227_);
v___x_2232_ = v___x_2221_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v___f_2223_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v___f_2230_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v___f_2229_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v___f_2228_);
v___x_2232_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2234_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___f_2224_);
lean_ctor_set(v___x_2214_, 0, v___x_2232_);
v___x_2234_ = v___x_2214_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___f_2224_);
v___x_2234_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_23948__overap_2238_; lean_object* v___x_2239_; 
v___x_2235_ = l_StateRefT_x27_instMonad___redArg(v___x_2234_);
v___x_2236_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2237_ = l_instInhabitedOfMonad___redArg(v___x_2235_, v___x_2236_);
v___x_23948__overap_2238_ = lean_panic_fn_borrowed(v___x_2237_, v_msg_2188_);
lean_dec(v___x_2237_);
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
lean_inc(v___y_2191_);
lean_inc_ref(v___y_2190_);
lean_inc(v___y_2189_);
v___x_2239_ = lean_apply_6(v___x_23948__overap_2238_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, lean_box(0));
return v___x_2239_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
return v_res_2253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2258_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
lean_ctor_set(v___x_2259_, 2, v___x_2258_);
lean_ctor_set(v___x_2259_, 3, v___x_2258_);
lean_ctor_set(v___x_2259_, 4, v___x_2257_);
lean_ctor_set(v___x_2259_, 5, v___x_2257_);
lean_ctor_set(v___x_2259_, 6, v___x_2257_);
lean_ctor_set(v___x_2259_, 7, v___x_2257_);
lean_ctor_set(v___x_2259_, 8, v___x_2257_);
lean_ctor_set(v___x_2259_, 9, v___x_2257_);
lean_ctor_set(v___x_2259_, 10, v___x_2257_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_unsigned_to_nat(32u);
v___x_2261_ = lean_mk_empty_array_with_capacity(v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2263_ = ((size_t)5ULL);
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = lean_unsigned_to_nat(32u);
v___x_2266_ = lean_mk_empty_array_with_capacity(v___x_2265_);
v___x_2267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2268_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v___x_2266_);
lean_ctor_set(v___x_2268_, 2, v___x_2264_);
lean_ctor_set(v___x_2268_, 3, v___x_2264_);
lean_ctor_set_usize(v___x_2268_, 4, v___x_2263_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2269_ = lean_box(1);
v___x_2270_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2271_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
lean_ctor_set(v___x_2272_, 1, v___x_2270_);
lean_ctor_set(v___x_2272_, 2, v___x_2269_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2278_ = l_Lean_stringToMessageData(v___x_2277_);
return v___x_2278_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2281_ = l_Lean_stringToMessageData(v___x_2280_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2284_ = l_Lean_stringToMessageData(v___x_2283_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2287_ = l_Lean_stringToMessageData(v___x_2286_);
return v___x_2287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2290_ = l_Lean_stringToMessageData(v___x_2289_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2293_ = l_Lean_stringToMessageData(v___x_2292_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__20));
v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__22));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__24));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__26));
v___x_2305_ = l_Lean_stringToMessageData(v___x_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2306_, lean_object* v_declHint_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_env_2312_; uint8_t v___x_2313_; 
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_st_ref_get(v___y_2308_);
v_env_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc_ref(v_env_2312_);
lean_dec(v___x_2311_);
v___x_2313_ = l_Lean_Name_isAnonymous(v_declHint_2307_);
if (v___x_2313_ == 0)
{
uint8_t v_isExporting_2314_; 
v_isExporting_2314_ = lean_ctor_get_uint8(v_env_2312_, sizeof(void*)*13);
if (v_isExporting_2314_ == 0)
{
lean_object* v___x_2315_; 
lean_dec_ref(v_env_2312_);
lean_dec(v_declHint_2307_);
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v_msg_2306_);
return v___x_2315_;
}
else
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
lean_inc_ref(v_env_2312_);
v___x_2316_ = l_Lean_Environment_setExporting(v_env_2312_, v___x_2313_);
lean_inc(v_declHint_2307_);
lean_inc_ref(v___x_2316_);
v___x_2317_ = l_Lean_Environment_contains(v___x_2316_, v_declHint_2307_, v_isExporting_2314_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; 
lean_dec_ref(v___x_2316_);
lean_dec_ref(v_env_2312_);
lean_dec(v_declHint_2307_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_msg_2306_);
return v___x_2318_;
}
else
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_c_2324_; lean_object* v___x_2325_; 
v___x_2319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2320_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2321_ = l_Lean_Options_empty;
lean_inc_ref(v___x_2316_);
v___x_2322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2316_);
lean_ctor_set(v___x_2322_, 1, v___x_2319_);
lean_ctor_set(v___x_2322_, 2, v___x_2320_);
lean_ctor_set(v___x_2322_, 3, v___x_2321_);
lean_inc(v_declHint_2307_);
v___x_2323_ = l_Lean_MessageData_ofConstName(v_declHint_2307_, v___x_2313_);
v_c_2324_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2324_, 0, v___x_2322_);
lean_ctor_set(v_c_2324_, 1, v___x_2323_);
v___x_2325_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_2316_, v_declHint_2307_);
lean_dec_ref(v___x_2316_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec_ref(v_env_2312_);
lean_dec(v_declHint_2307_);
v___x_2326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v_c_2324_);
v___x_2328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = l_Lean_MessageData_note(v___x_2329_);
v___x_2331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_msg_2306_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
return v___x_2332_;
}
else
{
lean_object* v_val_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2386_; 
v_val_2333_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2335_ = v___x_2325_;
v_isShared_2336_ = v_isSharedCheck_2386_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_val_2333_);
lean_dec(v___x_2325_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2386_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v_modules_2338_; lean_object* v_moduleNames_2339_; lean_object* v_mod_2340_; uint8_t v___x_2355_; 
v___x_2337_ = l_Lean_Environment_header(v_env_2312_);
lean_dec_ref(v_env_2312_);
v_modules_2338_ = lean_ctor_get(v___x_2337_, 3);
lean_inc_ref(v_modules_2338_);
v_moduleNames_2339_ = lean_ctor_get(v___x_2337_, 4);
lean_inc_ref(v_moduleNames_2339_);
lean_dec_ref(v___x_2337_);
v_mod_2340_ = lean_array_get(v___x_2310_, v_moduleNames_2339_, v_val_2333_);
lean_dec_ref(v_moduleNames_2339_);
v___x_2355_ = l_Lean_isPrivateName(v_declHint_2307_);
lean_dec(v_declHint_2307_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2356_ = lean_array_get_size(v_modules_2338_);
v___x_2357_ = lean_nat_dec_lt(v_val_2333_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_dec_ref(v_modules_2338_);
lean_dec(v_val_2333_);
goto v___jp_2341_;
}
else
{
lean_object* v___x_2358_; lean_object* v_toImport_2359_; uint8_t v_isExported_2360_; 
v___x_2358_ = lean_array_fget(v_modules_2338_, v_val_2333_);
lean_dec(v_val_2333_);
lean_dec_ref(v_modules_2338_);
v_toImport_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc_ref(v_toImport_2359_);
lean_dec(v___x_2358_);
v_isExported_2360_ = lean_ctor_get_uint8(v_toImport_2359_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2359_);
if (v_isExported_2360_ == 0)
{
goto v___jp_2341_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_del_object(v___x_2335_);
v___x_2361_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
lean_ctor_set(v___x_2362_, 1, v_c_2324_);
v___x_2363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = l_Lean_MessageData_ofName(v_mod_2340_);
lean_inc_ref(v___x_2365_);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21);
v___x_2368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2366_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2368_);
lean_ctor_set(v___x_2369_, 1, v___x_2365_);
v___x_2370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = l_Lean_MessageData_note(v___x_2371_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_msg_2306_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec_ref(v_modules_2338_);
lean_del_object(v___x_2335_);
lean_dec(v_val_2333_);
v___x_2375_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
lean_ctor_set(v___x_2376_, 1, v_c_2324_);
v___x_2377_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = l_Lean_MessageData_ofName(v_mod_2340_);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
v___x_2381_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27);
v___x_2382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2380_);
lean_ctor_set(v___x_2382_, 1, v___x_2381_);
v___x_2383_ = l_Lean_MessageData_note(v___x_2382_);
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v_msg_2306_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
v___jp_2341_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_c_2324_);
v___x_2344_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2343_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
v___x_2346_ = l_Lean_MessageData_ofName(v_mod_2340_);
v___x_2347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2345_);
lean_ctor_set(v___x_2347_, 1, v___x_2346_);
v___x_2348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = l_Lean_MessageData_note(v___x_2349_);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v_msg_2306_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2351_);
v___x_2353_ = v___x_2335_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2387_; 
lean_dec_ref(v_env_2312_);
lean_dec(v_declHint_2307_);
v___x_2387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_msg_2306_);
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2388_, lean_object* v_declHint_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2388_, v_declHint_2389_, v___y_2390_);
lean_dec(v___y_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2393_, lean_object* v_declHint_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v___x_2401_; lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2411_; 
v___x_2401_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2393_, v_declHint_2394_, v___y_2399_);
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2411_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2411_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2406_ = l_Lean_unknownIdentifierMessageTag;
v___x_2407_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2406_);
lean_ctor_set(v___x_2407_, 1, v_a_2402_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2407_);
v___x_2409_ = v___x_2404_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2412_, lean_object* v_declHint_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2412_, v_declHint_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_ref_2427_; lean_object* v___x_2428_; lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2437_; 
v_ref_2427_ = lean_ctor_get(v___y_2424_, 2);
v___x_2428_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2437_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
lean_inc(v_ref_2427_);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_ref_2427_);
lean_ctor_set(v___x_2433_, 1, v_a_2429_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 1);
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2433_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2445_, lean_object* v_msg_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_toCold_2453_; lean_object* v_currRecDepth_2454_; lean_object* v_ref_2455_; uint16_t v_optionFlags_2456_; uint8_t v_suppressElabErrors_2457_; uint8_t v_checkDeprecated_2458_; uint8_t v_isRecordingDeps_2459_; lean_object* v_ref_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_toCold_2453_ = lean_ctor_get(v___y_2450_, 0);
v_currRecDepth_2454_ = lean_ctor_get(v___y_2450_, 1);
v_ref_2455_ = lean_ctor_get(v___y_2450_, 2);
v_optionFlags_2456_ = lean_ctor_get_uint16(v___y_2450_, sizeof(void*)*3);
v_suppressElabErrors_2457_ = lean_ctor_get_uint8(v___y_2450_, sizeof(void*)*3 + 2);
v_checkDeprecated_2458_ = lean_ctor_get_uint8(v___y_2450_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2459_ = lean_ctor_get_uint8(v___y_2450_, sizeof(void*)*3 + 4);
v_ref_2460_ = l_Lean_replaceRef(v_ref_2445_, v_ref_2455_);
lean_inc(v_currRecDepth_2454_);
lean_inc_ref(v_toCold_2453_);
v___x_2461_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2461_, 0, v_toCold_2453_);
lean_ctor_set(v___x_2461_, 1, v_currRecDepth_2454_);
lean_ctor_set(v___x_2461_, 2, v_ref_2460_);
lean_ctor_set_uint16(v___x_2461_, sizeof(void*)*3, v_optionFlags_2456_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*3 + 2, v_suppressElabErrors_2457_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*3 + 3, v_checkDeprecated_2458_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*3 + 4, v_isRecordingDeps_2459_);
v___x_2462_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2446_, v___y_2448_, v___y_2449_, v___x_2461_, v___y_2451_);
lean_dec_ref_known(v___x_2461_, 3);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2463_, lean_object* v_msg_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2463_, v_msg_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec(v_ref_2463_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2472_, lean_object* v_msg_2473_, lean_object* v_declHint_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v___x_2481_; lean_object* v_a_2482_; lean_object* v___x_2483_; 
v___x_2481_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2473_, v_declHint_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref(v___x_2481_);
v___x_2483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2472_, v_a_2482_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2484_, lean_object* v_msg_2485_, lean_object* v_declHint_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2484_, v_msg_2485_, v_declHint_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v_ref_2484_);
return v_res_2493_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2496_ = l_Lean_stringToMessageData(v___x_2495_);
return v___x_2496_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2499_ = l_Lean_stringToMessageData(v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2500_, lean_object* v_constName_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; uint8_t v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2508_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2509_ = 0;
lean_inc(v_constName_2501_);
v___x_2510_ = l_Lean_MessageData_ofConstName(v_constName_2501_, v___x_2509_);
v___x_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2508_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2500_, v___x_2513_, v_constName_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2515_, lean_object* v_constName_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2515_, v_constName_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec(v_ref_2515_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_ref_2531_; lean_object* v___x_2532_; 
v_ref_2531_ = lean_ctor_get(v___y_2528_, 2);
v___x_2532_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2531_, v_constName_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_){
_start:
{
lean_object* v___x_2548_; lean_object* v_env_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = lean_st_ref_get(v___y_2546_);
v_env_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc_ref(v_env_2549_);
lean_dec(v___x_2548_);
v___x_2550_ = 0;
lean_inc(v_constName_2541_);
v___x_2551_ = l_Lean_Environment_find_x3f(v_env_2549_, v_constName_2541_, v___x_2550_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
return v___x_2552_;
}
else
{
lean_object* v_val_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_constName_2541_);
v_val_2553_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2551_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_val_2553_);
lean_dec(v___x_2551_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 0);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_val_2553_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
return v_res_2568_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2572_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2573_ = lean_unsigned_to_nat(53u);
v___x_2574_ = lean_unsigned_to_nat(62u);
v___x_2575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2577_ = l_mkPanicMessageWithDecl(v___x_2576_, v___x_2575_, v___x_2574_, v___x_2573_, v___x_2572_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2578_, size_t v_i_2579_, lean_object* v_bs_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
uint8_t v___x_2587_; 
v___x_2587_ = lean_usize_dec_lt(v_i_2579_, v_sz_2578_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2588_, 0, v_bs_2580_);
return v___x_2588_;
}
else
{
lean_object* v_v_2589_; lean_object* v___x_2590_; lean_object* v_bs_x27_2591_; lean_object* v_a_2593_; lean_object* v___x_2598_; 
v_v_2589_ = lean_array_uget(v_bs_2580_, v_i_2579_);
v___x_2590_ = lean_unsigned_to_nat(0u);
v_bs_x27_2591_ = lean_array_uset(v_bs_2580_, v_i_2579_, v___x_2590_);
v___x_2598_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2589_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v_a_2599_; 
v_a_2599_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2598_, 1);
if (lean_obj_tag(v_a_2599_) == 6)
{
lean_object* v_val_2600_; lean_object* v_numFields_2601_; uint8_t v___x_2602_; lean_object* v___x_2603_; 
v_val_2600_ = lean_ctor_get(v_a_2599_, 0);
lean_inc_ref(v_val_2600_);
lean_dec_ref_known(v_a_2599_, 1);
v_numFields_2601_ = lean_ctor_get(v_val_2600_, 4);
lean_inc(v_numFields_2601_);
lean_dec_ref(v_val_2600_);
v___x_2602_ = 0;
v___x_2603_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2603_, 0, v_numFields_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2590_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*2, v___x_2602_);
v_a_2593_ = v___x_2603_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_dec(v_a_2599_);
v___x_2604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2605_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2604_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v_a_2593_ = v_a_2606_;
goto v___jp_2592_;
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_bs_x27_2591_);
v_a_2607_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2605_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2605_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_bs_x27_2591_);
v_a_2615_ = lean_ctor_get(v___x_2598_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2598_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2598_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2598_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
v___jp_2592_:
{
size_t v___x_2594_; size_t v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = ((size_t)1ULL);
v___x_2595_ = lean_usize_add(v_i_2579_, v___x_2594_);
v___x_2596_ = lean_array_uset(v_bs_x27_2591_, v_i_2579_, v_a_2593_);
v_i_2579_ = v___x_2595_;
v_bs_2580_ = v___x_2596_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2623_, lean_object* v_i_2624_, lean_object* v_bs_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
size_t v_sz_boxed_2632_; size_t v_i_boxed_2633_; lean_object* v_res_2634_; 
v_sz_boxed_2632_ = lean_unbox_usize(v_sz_2623_);
lean_dec(v_sz_2623_);
v_i_boxed_2633_ = lean_unbox_usize(v_i_2624_);
lean_dec(v_i_2624_);
v_res_2634_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2632_, v_i_boxed_2633_, v_bs_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
return v_res_2634_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_box(0);
v___x_2636_ = lean_unsigned_to_nat(16u);
v___x_2637_ = lean_mk_array(v___x_2636_, v___x_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v___x_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2643_, uint8_t v_alsoCasesOn_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
uint8_t v___x_2654_; 
v___x_2654_ = l_Lean_Expr_isApp(v_e_2643_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_dec_ref(v_e_2643_);
v___x_2655_ = lean_box(0);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Expr_getAppFn(v_e_2643_);
if (lean_obj_tag(v___x_2657_) == 4)
{
lean_object* v_declName_2658_; lean_object* v_us_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2814_; 
v_declName_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_n(v_declName_2658_, 2);
v_us_2659_ = lean_ctor_get(v___x_2657_, 1);
lean_inc(v_us_2659_);
lean_dec_ref_known(v___x_2657_, 2);
v___x_2660_ = l_Lean_instInhabitedExpr;
v___x_2661_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2658_, v___y_2649_);
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2664_ = v___x_2661_;
v_isShared_2665_ = v_isSharedCheck_2814_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2661_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2814_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
if (lean_obj_tag(v_a_2662_) == 1)
{
lean_object* v_val_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2707_; 
v_val_2666_ = lean_ctor_get(v_a_2662_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v_a_2662_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2668_ = v_a_2662_;
v_isShared_2669_ = v_isSharedCheck_2707_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_val_2666_);
lean_dec(v_a_2662_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2707_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_dummy_2670_; lean_object* v_nargs_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v_args_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_dummy_2670_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2671_ = l_Lean_Expr_getAppNumArgs(v_e_2643_);
lean_inc(v_nargs_2671_);
v___x_2672_ = lean_mk_array(v_nargs_2671_, v_dummy_2670_);
v___x_2673_ = lean_unsigned_to_nat(1u);
v___x_2674_ = lean_nat_sub(v_nargs_2671_, v___x_2673_);
lean_dec(v_nargs_2671_);
v_args_2675_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2643_, v___x_2672_, v___x_2674_);
v___x_2676_ = lean_array_get_size(v_args_2675_);
v___x_2677_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2666_);
v___x_2678_ = lean_nat_dec_lt(v___x_2676_, v___x_2677_);
lean_dec(v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v_numParams_2679_; lean_object* v_numDiscrs_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2698_; 
v_numParams_2679_ = lean_ctor_get(v_val_2666_, 0);
v_numDiscrs_2680_ = lean_ctor_get(v_val_2666_, 1);
v___x_2681_ = lean_array_mk(v_us_2659_);
v___x_2682_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2679_);
v___x_2683_ = l_Array_extract___redArg(v_args_2675_, v___x_2682_, v_numParams_2679_);
v___x_2684_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2666_);
v___x_2685_ = lean_array_get(v___x_2660_, v_args_2675_, v___x_2684_);
lean_dec(v___x_2684_);
v___x_2686_ = lean_nat_add(v_numParams_2679_, v___x_2673_);
v___x_2687_ = lean_nat_add(v___x_2686_, v_numDiscrs_2680_);
lean_inc(v___x_2687_);
lean_inc_ref_n(v_args_2675_, 2);
v___x_2688_ = l_Array_toSubarray___redArg(v_args_2675_, v___x_2686_, v___x_2687_);
v___x_2689_ = l_Subarray_copy___redArg(v___x_2688_);
v___x_2690_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2666_);
v___x_2691_ = lean_nat_add(v___x_2687_, v___x_2690_);
lean_dec(v___x_2690_);
lean_inc(v___x_2691_);
v___x_2692_ = l_Array_toSubarray___redArg(v_args_2675_, v___x_2687_, v___x_2691_);
v___x_2693_ = l_Subarray_copy___redArg(v___x_2692_);
v___x_2694_ = l_Array_toSubarray___redArg(v_args_2675_, v___x_2691_, v___x_2676_);
v___x_2695_ = l_Subarray_copy___redArg(v___x_2694_);
v___x_2696_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2696_, 0, v_val_2666_);
lean_ctor_set(v___x_2696_, 1, v_declName_2658_);
lean_ctor_set(v___x_2696_, 2, v___x_2681_);
lean_ctor_set(v___x_2696_, 3, v___x_2683_);
lean_ctor_set(v___x_2696_, 4, v___x_2685_);
lean_ctor_set(v___x_2696_, 5, v___x_2689_);
lean_ctor_set(v___x_2696_, 6, v___x_2693_);
lean_ctor_set(v___x_2696_, 7, v___x_2695_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2696_);
v___x_2698_ = v___x_2668_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2700_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2698_);
v___x_2700_ = v___x_2664_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
lean_dec_ref(v_args_2675_);
lean_del_object(v___x_2668_);
lean_dec(v_val_2666_);
lean_dec(v_us_2659_);
lean_dec(v_declName_2658_);
v___x_2703_ = lean_box(0);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2703_);
v___x_2705_ = v___x_2664_;
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
}
else
{
lean_object* v___x_2708_; 
lean_del_object(v___x_2664_);
lean_dec(v_a_2662_);
v___x_2708_ = lean_st_ref_get(v___y_2649_);
if (v_alsoCasesOn_2644_ == 0)
{
lean_dec(v___x_2708_);
lean_dec(v_us_2659_);
lean_dec(v_declName_2658_);
lean_dec_ref(v_e_2643_);
goto v___jp_2651_;
}
else
{
lean_object* v_env_2709_; uint8_t v___x_2710_; 
v_env_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc_ref(v_env_2709_);
lean_dec(v___x_2708_);
lean_inc(v_declName_2658_);
v___x_2710_ = l_Lean_isCasesOnRecursor(v_env_2709_, v_declName_2658_);
if (v___x_2710_ == 0)
{
lean_dec(v_us_2659_);
lean_dec(v_declName_2658_);
lean_dec_ref(v_e_2643_);
goto v___jp_2651_;
}
else
{
lean_object* v_indName_2711_; lean_object* v___x_2712_; 
v_indName_2711_ = l_Lean_Name_getPrefix(v_declName_2658_);
v___x_2712_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2711_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2805_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2715_ = v___x_2712_;
v_isShared_2716_ = v_isSharedCheck_2805_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_a_2713_);
lean_dec(v___x_2712_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2805_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
if (lean_obj_tag(v_a_2713_) == 5)
{
lean_object* v_val_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2800_; 
v_val_2717_ = lean_ctor_get(v_a_2713_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_a_2713_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2719_ = v_a_2713_;
v_isShared_2720_ = v_isSharedCheck_2800_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_val_2717_);
lean_dec(v_a_2713_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2800_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_toConstantVal_2721_; lean_object* v_numParams_2722_; lean_object* v_numIndices_2723_; lean_object* v_ctors_2724_; lean_object* v_nargs_2725_; lean_object* v_dummy_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v_args_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v_toConstantVal_2721_ = lean_ctor_get(v_val_2717_, 0);
lean_inc_ref(v_toConstantVal_2721_);
v_numParams_2722_ = lean_ctor_get(v_val_2717_, 1);
lean_inc(v_numParams_2722_);
v_numIndices_2723_ = lean_ctor_get(v_val_2717_, 2);
lean_inc(v_numIndices_2723_);
v_ctors_2724_ = lean_ctor_get(v_val_2717_, 4);
lean_inc(v_ctors_2724_);
v_nargs_2725_ = l_Lean_Expr_getAppNumArgs(v_e_2643_);
v_dummy_2726_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2725_);
v___x_2727_ = lean_mk_array(v_nargs_2725_, v_dummy_2726_);
v___x_2728_ = lean_unsigned_to_nat(1u);
v___x_2729_ = lean_nat_sub(v_nargs_2725_, v___x_2728_);
lean_dec(v_nargs_2725_);
v_args_2730_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2643_, v___x_2727_, v___x_2729_);
v___x_2731_ = lean_nat_add(v_numParams_2722_, v___x_2728_);
v___x_2732_ = lean_nat_add(v___x_2731_, v_numIndices_2723_);
v___x_2733_ = lean_nat_add(v___x_2732_, v___x_2728_);
lean_dec(v___x_2732_);
v___x_2734_ = l_Lean_InductiveVal_numCtors(v_val_2717_);
lean_dec_ref(v_val_2717_);
v___x_2735_ = lean_nat_add(v___x_2733_, v___x_2734_);
lean_dec(v___x_2734_);
v___x_2736_ = lean_array_get_size(v_args_2730_);
v___x_2737_ = lean_nat_dec_le(v___x_2735_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_dec(v___x_2735_);
lean_dec(v___x_2733_);
lean_dec(v___x_2731_);
lean_dec_ref(v_args_2730_);
lean_dec(v_ctors_2724_);
lean_dec(v_numIndices_2723_);
lean_dec(v_numParams_2722_);
lean_dec_ref(v_toConstantVal_2721_);
lean_del_object(v___x_2719_);
lean_dec(v_us_2659_);
lean_dec(v_declName_2658_);
v___x_2738_ = lean_box(0);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2738_);
v___x_2740_ = v___x_2715_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
else
{
lean_object* v___x_2742_; lean_object* v_params_2743_; lean_object* v_motive_2744_; lean_object* v_discrs_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v_discrInfos_2748_; lean_object* v_alts_2749_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v_lower_2791_; lean_object* v_upper_2792_; uint8_t v___x_2799_; 
lean_del_object(v___x_2715_);
v___x_2742_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2722_);
lean_inc_ref_n(v_args_2730_, 3);
v_params_2743_ = l_Array_toSubarray___redArg(v_args_2730_, v___x_2742_, v_numParams_2722_);
v_motive_2744_ = lean_array_get(v___x_2660_, v_args_2730_, v_numParams_2722_);
lean_dec(v_numParams_2722_);
lean_inc(v___x_2733_);
v_discrs_2745_ = l_Array_toSubarray___redArg(v_args_2730_, v___x_2731_, v___x_2733_);
v___x_2746_ = lean_nat_add(v_numIndices_2723_, v___x_2728_);
lean_dec(v_numIndices_2723_);
v___x_2747_ = lean_box(0);
v_discrInfos_2748_ = lean_mk_array(v___x_2746_, v___x_2747_);
lean_inc(v___x_2735_);
v_alts_2749_ = l_Array_toSubarray___redArg(v_args_2730_, v___x_2733_, v___x_2735_);
v___x_2799_ = lean_nat_dec_le(v___x_2735_, v___x_2742_);
if (v___x_2799_ == 0)
{
v_lower_2791_ = v___x_2735_;
v_upper_2792_ = v___x_2736_;
goto v___jp_2790_;
}
else
{
lean_dec(v___x_2735_);
v_lower_2791_ = v___x_2742_;
v_upper_2792_ = v___x_2736_;
goto v___jp_2790_;
}
v___jp_2750_:
{
lean_object* v___x_2753_; size_t v_sz_2754_; size_t v___x_2755_; lean_object* v___x_2756_; 
v___x_2753_ = lean_array_mk(v_ctors_2724_);
v_sz_2754_ = lean_array_size(v___x_2753_);
v___x_2755_ = ((size_t)0ULL);
v___x_2756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2754_, v___x_2755_, v___x_2753_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2781_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2781_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2781_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v_start_2761_; lean_object* v_stop_2762_; lean_object* v_start_2763_; lean_object* v_stop_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v_start_2761_ = lean_ctor_get(v_params_2743_, 1);
v_stop_2762_ = lean_ctor_get(v_params_2743_, 2);
v_start_2763_ = lean_ctor_get(v_discrs_2745_, 1);
v_stop_2764_ = lean_ctor_get(v_discrs_2745_, 2);
v___x_2765_ = lean_nat_sub(v_stop_2762_, v_start_2761_);
v___x_2766_ = lean_nat_sub(v_stop_2764_, v_start_2763_);
v___x_2767_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2768_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2765_);
lean_ctor_set(v___x_2768_, 1, v___x_2766_);
lean_ctor_set(v___x_2768_, 2, v_a_2757_);
lean_ctor_set(v___x_2768_, 3, v___y_2752_);
lean_ctor_set(v___x_2768_, 4, v_discrInfos_2748_);
lean_ctor_set(v___x_2768_, 5, v___x_2767_);
v___x_2769_ = lean_array_mk(v_us_2659_);
v___x_2770_ = l_Subarray_copy___redArg(v_params_2743_);
v___x_2771_ = l_Subarray_copy___redArg(v_discrs_2745_);
v___x_2772_ = l_Subarray_copy___redArg(v_alts_2749_);
v___x_2773_ = l_Subarray_copy___redArg(v___y_2751_);
v___x_2774_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2768_);
lean_ctor_set(v___x_2774_, 1, v_declName_2658_);
lean_ctor_set(v___x_2774_, 2, v___x_2769_);
lean_ctor_set(v___x_2774_, 3, v___x_2770_);
lean_ctor_set(v___x_2774_, 4, v_motive_2744_);
lean_ctor_set(v___x_2774_, 5, v___x_2771_);
lean_ctor_set(v___x_2774_, 6, v___x_2772_);
lean_ctor_set(v___x_2774_, 7, v___x_2773_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set_tag(v___x_2719_, 1);
lean_ctor_set(v___x_2719_, 0, v___x_2774_);
v___x_2776_ = v___x_2719_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2774_);
v___x_2776_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2778_; 
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2776_);
v___x_2778_ = v___x_2759_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec_ref(v_alts_2749_);
lean_dec_ref(v_discrInfos_2748_);
lean_dec_ref(v_discrs_2745_);
lean_dec(v_motive_2744_);
lean_dec_ref(v_params_2743_);
lean_del_object(v___x_2719_);
lean_dec(v_us_2659_);
lean_dec(v_declName_2658_);
v_a_2782_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2756_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2756_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
v___jp_2790_:
{
lean_object* v_levelParams_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_levelParams_2793_ = lean_ctor_get(v_toConstantVal_2721_, 1);
lean_inc(v_levelParams_2793_);
lean_dec_ref(v_toConstantVal_2721_);
v___x_2794_ = l_Array_toSubarray___redArg(v_args_2730_, v_lower_2791_, v_upper_2792_);
v___x_2795_ = l_List_lengthTR___redArg(v_levelParams_2793_);
lean_dec(v_levelParams_2793_);
v___x_2796_ = l_List_lengthTR___redArg(v_us_2659_);
v___x_2797_ = lean_nat_dec_eq(v___x_2795_, v___x_2796_);
lean_dec(v___x_2796_);
lean_dec(v___x_2795_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2751_ = v___x_2794_;
v___y_2752_ = v___x_2798_;
goto v___jp_2750_;
}
else
{
v___y_2751_ = v___x_2794_;
v___y_2752_ = v___x_2747_;
goto v___jp_2750_;
}
}
}
}
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
lean_dec(v_a_2713_);
lean_dec(v_us_2659_);
lean_dec(v_declName_2658_);
lean_dec_ref(v_e_2643_);
v___x_2801_ = lean_box(0);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2801_);
v___x_2803_ = v___x_2715_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec(v_us_2659_);
lean_dec(v_declName_2658_);
lean_dec_ref(v_e_2643_);
v_a_2806_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2712_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2712_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
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
lean_dec_ref(v___x_2657_);
lean_dec_ref(v_e_2643_);
goto v___jp_2651_;
}
}
v___jp_2651_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_box(0);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2815_, lean_object* v_alsoCasesOn_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2823_; lean_object* v_res_2824_; 
v_alsoCasesOn_boxed_2823_ = lean_unbox(v_alsoCasesOn_2816_);
v_res_2824_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2815_, v_alsoCasesOn_boxed_2823_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
if (lean_obj_tag(v_a_2825_) == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = l_List_reverse___redArg(v_a_2826_);
return v___x_2827_;
}
else
{
lean_object* v_head_2828_; lean_object* v_tail_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2838_; 
v_head_2828_ = lean_ctor_get(v_a_2825_, 0);
v_tail_2829_ = lean_ctor_get(v_a_2825_, 1);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_a_2825_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2831_ = v_a_2825_;
v_isShared_2832_ = v_isSharedCheck_2838_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_tail_2829_);
lean_inc(v_head_2828_);
lean_dec(v_a_2825_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2838_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = l_Lean_MessageData_ofExpr(v_head_2828_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v_a_2826_);
lean_ctor_set(v___x_2831_, 0, v___x_2833_);
v___x_2835_ = v___x_2831_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_a_2826_);
v___x_2835_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
v_a_2825_ = v_tail_2829_;
v_a_2826_ = v___x_2835_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2839_, lean_object* v_as_2840_, size_t v_i_2841_, size_t v_stop_2842_){
_start:
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_usize_dec_eq(v_i_2841_, v_stop_2842_);
if (v___x_2843_ == 0)
{
lean_object* v___x_2844_; lean_object* v_fnName_2845_; lean_object* v_recArgPos_2846_; uint8_t v___x_2847_; 
v___x_2844_ = lean_array_uget_borrowed(v_as_2840_, v_i_2841_);
v_fnName_2845_ = lean_ctor_get(v___x_2844_, 0);
v_recArgPos_2846_ = lean_ctor_get(v___x_2844_, 2);
lean_inc(v_recArgPos_2846_);
lean_inc(v_fnName_2845_);
v___x_2847_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2845_, v_recArgPos_2846_, v_e_2839_);
if (v___x_2847_ == 0)
{
size_t v___x_2848_; size_t v___x_2849_; 
v___x_2848_ = ((size_t)1ULL);
v___x_2849_ = lean_usize_add(v_i_2841_, v___x_2848_);
v_i_2841_ = v___x_2849_;
goto _start;
}
else
{
return v___x_2847_;
}
}
else
{
uint8_t v___x_2851_; 
v___x_2851_ = 0;
return v___x_2851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2852_, lean_object* v_as_2853_, lean_object* v_i_2854_, lean_object* v_stop_2855_){
_start:
{
size_t v_i_boxed_2856_; size_t v_stop_boxed_2857_; uint8_t v_res_2858_; lean_object* v_r_2859_; 
v_i_boxed_2856_ = lean_unbox_usize(v_i_2854_);
lean_dec(v_i_2854_);
v_stop_boxed_2857_ = lean_unbox_usize(v_stop_2855_);
lean_dec(v_stop_2855_);
v_res_2858_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2852_, v_as_2853_, v_i_boxed_2856_, v_stop_boxed_2857_);
lean_dec_ref(v_as_2853_);
lean_dec_ref(v_e_2852_);
v_r_2859_ = lean_box(v_res_2858_);
return v_r_2859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2860_, lean_object* v_____do__lift_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v_toCold_2868_; lean_object* v_options_2869_; uint8_t v_hasTrace_2870_; 
v_toCold_2868_ = lean_ctor_get(v___y_2865_, 0);
v_options_2869_ = lean_ctor_get(v_toCold_2868_, 2);
v_hasTrace_2870_ = lean_ctor_get_uint8(v_options_2869_, sizeof(void*)*1);
if (v_hasTrace_2870_ == 0)
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec(v___x_2860_);
v___x_2871_ = lean_box(v_hasTrace_2870_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2874_ = l_Lean_Name_append(v___x_2873_, v___x_2860_);
v___x_2875_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2861_, v_options_2869_, v___x_2874_);
lean_dec(v___x_2874_);
v___x_2876_ = lean_box(v___x_2875_);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2878_, lean_object* v_____do__lift_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2878_, v_____do__lift_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v_____do__lift_2879_);
return v_res_2886_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2887_, lean_object* v_x_2888_){
_start:
{
lean_object* v_fnName_2889_; uint8_t v___x_2890_; 
v_fnName_2889_ = lean_ctor_get(v_x_2888_, 0);
v___x_2890_ = l_Lean_Expr_isConstOf(v_x_2887_, v_fnName_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2891_, lean_object* v_x_2892_){
_start:
{
uint8_t v_res_2893_; lean_object* v_r_2894_; 
v_res_2893_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2891_, v_x_2892_);
lean_dec_ref(v_x_2892_);
lean_dec_ref(v_x_2891_);
v_r_2894_ = lean_box(v_res_2893_);
return v_r_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2895_, lean_object* v_type_2896_, lean_object* v_val_2897_, lean_object* v_k_2898_, uint8_t v_nondep_2899_, uint8_t v_kind_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___f_2907_; lean_object* v___x_2908_; 
lean_inc(v___y_2901_);
v___f_2907_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2907_, 0, v_k_2898_);
lean_closure_set(v___f_2907_, 1, v___y_2901_);
v___x_2908_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2895_, v_type_2896_, v_val_2897_, v___f_2907_, v_nondep_2899_, v_kind_2900_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
if (lean_obj_tag(v___x_2908_) == 0)
{
return v___x_2908_;
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2908_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2908_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2917_, lean_object* v_type_2918_, lean_object* v_val_2919_, lean_object* v_k_2920_, lean_object* v_nondep_2921_, lean_object* v_kind_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
uint8_t v_nondep_boxed_2929_; uint8_t v_kind_boxed_2930_; lean_object* v_res_2931_; 
v_nondep_boxed_2929_ = lean_unbox(v_nondep_2921_);
v_kind_boxed_2930_ = lean_unbox(v_kind_2922_);
v_res_2931_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2917_, v_type_2918_, v_val_2919_, v_k_2920_, v_nondep_boxed_2929_, v_kind_boxed_2930_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
lean_dec(v___y_2923_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2932_, uint8_t v_usedLetOnly_2933_, lean_object* v_x_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; 
lean_inc(v___y_2939_);
lean_inc_ref(v___y_2938_);
lean_inc(v___y_2937_);
lean_inc_ref(v___y_2936_);
lean_inc(v___y_2935_);
lean_inc_ref(v_x_2934_);
v___x_2941_ = lean_apply_7(v_k_2932_, v_x_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, lean_box(0));
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; uint8_t v___x_2947_; lean_object* v___x_2948_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref_known(v___x_2941_, 1);
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_mk_empty_array_with_capacity(v___x_2943_);
v___x_2945_ = lean_array_push(v___x_2944_, v_x_2934_);
v___x_2946_ = 0;
v___x_2947_ = 1;
v___x_2948_ = l_Lean_Meta_mkLetFVars(v___x_2945_, v_a_2942_, v_usedLetOnly_2933_, v___x_2946_, v___x_2947_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec_ref(v___x_2945_);
return v___x_2948_;
}
else
{
lean_dec_ref(v_x_2934_);
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2949_, lean_object* v_usedLetOnly_2950_, lean_object* v_x_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
uint8_t v_usedLetOnly_boxed_2958_; lean_object* v_res_2959_; 
v_usedLetOnly_boxed_2958_ = lean_unbox(v_usedLetOnly_2950_);
v_res_2959_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2949_, v_usedLetOnly_boxed_2958_, v_x_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec(v___y_2954_);
lean_dec_ref(v___y_2953_);
lean_dec(v___y_2952_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2960_, lean_object* v_type_2961_, lean_object* v_val_2962_, lean_object* v_k_2963_, uint8_t v_nondep_2964_, uint8_t v_kind_2965_, uint8_t v_usedLetOnly_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v___x_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; 
v___x_2973_ = lean_box(v_usedLetOnly_2966_);
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2974_, 0, v_k_2963_);
lean_closure_set(v___f_2974_, 1, v___x_2973_);
v___x_2975_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2960_, v_type_2961_, v_val_2962_, v___f_2974_, v_nondep_2964_, v_kind_2965_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2976_, lean_object* v_type_2977_, lean_object* v_val_2978_, lean_object* v_k_2979_, lean_object* v_nondep_2980_, lean_object* v_kind_2981_, lean_object* v_usedLetOnly_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v_nondep_boxed_2989_; uint8_t v_kind_boxed_2990_; uint8_t v_usedLetOnly_boxed_2991_; lean_object* v_res_2992_; 
v_nondep_boxed_2989_ = lean_unbox(v_nondep_2980_);
v_kind_boxed_2990_ = lean_unbox(v_kind_2981_);
v_usedLetOnly_boxed_2991_ = lean_unbox(v_usedLetOnly_2982_);
v_res_2992_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2976_, v_type_2977_, v_val_2978_, v_k_2979_, v_nondep_boxed_2989_, v_kind_boxed_2990_, v_usedLetOnly_boxed_2991_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_2993_, lean_object* v_positions_2994_, lean_object* v_recFnNames_2995_, lean_object* v_containsRecFn_2996_, lean_object* v_below_2997_, size_t v_sz_2998_, size_t v_i_2999_, lean_object* v_bs_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
uint8_t v___x_3007_; 
v___x_3007_ = lean_usize_dec_lt(v_i_2999_, v_sz_2998_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec_ref(v_below_2997_);
lean_dec_ref(v_containsRecFn_2996_);
lean_dec_ref(v_recFnNames_2995_);
lean_dec_ref(v_positions_2994_);
lean_dec_ref(v_recArgInfos_2993_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v_bs_3000_);
return v___x_3008_;
}
else
{
lean_object* v_v_3009_; lean_object* v___x_3010_; lean_object* v_bs_x27_3011_; lean_object* v___x_3012_; 
v_v_3009_ = lean_array_uget(v_bs_3000_, v_i_2999_);
v___x_3010_ = lean_unsigned_to_nat(0u);
v_bs_x27_3011_ = lean_array_uset(v_bs_3000_, v_i_2999_, v___x_3010_);
lean_inc_ref(v___y_3004_);
lean_inc_ref(v_below_2997_);
lean_inc_ref(v_containsRecFn_2996_);
lean_inc_ref(v_recFnNames_2995_);
lean_inc_ref(v_positions_2994_);
lean_inc_ref(v_recArgInfos_2993_);
v___x_3012_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_2993_, v_positions_2994_, v_recFnNames_2995_, v_containsRecFn_2996_, v_below_2997_, v_v_3009_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; size_t v___x_3014_; size_t v___x_3015_; lean_object* v___x_3016_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = ((size_t)1ULL);
v___x_3015_ = lean_usize_add(v_i_2999_, v___x_3014_);
v___x_3016_ = lean_array_uset(v_bs_x27_3011_, v_i_2999_, v_a_3013_);
v_i_2999_ = v___x_3015_;
v_bs_3000_ = v___x_3016_;
goto _start;
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
lean_dec_ref(v_bs_x27_3011_);
lean_dec_ref(v_below_2997_);
lean_dec_ref(v_containsRecFn_2996_);
lean_dec_ref(v_recFnNames_2995_);
lean_dec_ref(v_positions_2994_);
lean_dec_ref(v_recArgInfos_2993_);
v_a_3018_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3012_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3012_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3028_ = l_Lean_stringToMessageData(v___x_3027_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3031_ = l_Lean_stringToMessageData(v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3032_, lean_object* v_positions_3033_, lean_object* v_recFnNames_3034_, lean_object* v_containsRecFn_3035_, lean_object* v_below_3036_, lean_object* v_e_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
if (lean_obj_tag(v_x_3038_) == 5)
{
lean_object* v_fn_3047_; lean_object* v_arg_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v_fn_3047_ = lean_ctor_get(v_x_3038_, 0);
lean_inc_ref(v_fn_3047_);
v_arg_3048_ = lean_ctor_get(v_x_3038_, 1);
lean_inc_ref(v_arg_3048_);
lean_dec_ref_known(v_x_3038_, 2);
v___x_3049_ = lean_array_set(v_x_3039_, v_x_3040_, v_arg_3048_);
v___x_3050_ = lean_unsigned_to_nat(1u);
v___x_3051_ = lean_nat_sub(v_x_3040_, v___x_3050_);
lean_dec(v_x_3040_);
v_x_3038_ = v_fn_3047_;
v_x_3039_ = v___x_3049_;
v_x_3040_ = v___x_3051_;
goto _start;
}
else
{
lean_object* v___f_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec(v_x_3040_);
lean_inc_ref(v_x_3038_);
v___f_3053_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3053_, 0, v_x_3038_);
v___x_3054_ = lean_unsigned_to_nat(0u);
v___x_3055_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3053_, v_recArgInfos_3032_, v___x_3054_);
if (lean_obj_tag(v___x_3055_) == 1)
{
lean_object* v_val_3056_; lean_object* v___x_3057_; lean_object* v_fixedParamPerm_3058_; lean_object* v_recArgPos_3059_; lean_object* v_indGroupInst_3060_; lean_object* v_a_3062_; lean_object* v___x_3086_; uint8_t v___x_3087_; 
lean_dec_ref(v_x_3038_);
v_val_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_val_3056_);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3057_ = lean_array_fget_borrowed(v_recArgInfos_3032_, v_val_3056_);
v_fixedParamPerm_3058_ = lean_ctor_get(v___x_3057_, 1);
v_recArgPos_3059_ = lean_ctor_get(v___x_3057_, 2);
v_indGroupInst_3060_ = lean_ctor_get(v___x_3057_, 4);
v___x_3086_ = lean_array_get_size(v_x_3039_);
v___x_3087_ = lean_nat_dec_lt(v_recArgPos_3059_, v___x_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec(v_val_3056_);
lean_dec_ref(v_x_3039_);
lean_dec_ref(v_below_3036_);
lean_dec_ref(v_containsRecFn_3035_);
lean_dec_ref(v_recFnNames_3034_);
lean_dec_ref(v_positions_3033_);
lean_dec_ref(v_recArgInfos_3032_);
v___x_3088_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3089_ = l_Lean_indentExpr(v_e_3037_);
v___x_3090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3088_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3090_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3091_;
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3092_ = lean_array_fget_borrowed(v_x_3039_, v_recArgPos_3059_);
lean_inc_ref(v___y_3044_);
lean_inc(v___x_3092_);
lean_inc_ref(v_below_3036_);
lean_inc_ref(v_containsRecFn_3035_);
lean_inc_ref(v_recFnNames_3034_);
lean_inc_ref(v_positions_3033_);
lean_inc_ref(v_recArgInfos_3032_);
v___x_3093_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3032_, v_positions_3033_, v_recFnNames_3034_, v_containsRecFn_3035_, v_below_3036_, v___x_3092_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v_params_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
v_params_3095_ = lean_ctor_get(v_indGroupInst_3060_, 2);
v___x_3096_ = lean_array_get_size(v_params_3095_);
lean_inc_ref(v_positions_3033_);
lean_inc_ref(v_below_3036_);
v___x_3097_ = l_Lean_Elab_Structural_toBelow(v_below_3036_, v___x_3096_, v_positions_3033_, v_val_3056_, v_a_3094_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; 
lean_dec_ref(v_e_3037_);
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v_a_3062_ = v_a_3098_;
goto v___jp_3061_;
}
else
{
lean_object* v_a_3099_; uint8_t v___x_3100_; 
lean_dec_ref(v_x_3039_);
lean_dec_ref(v_below_3036_);
lean_dec_ref(v_containsRecFn_3035_);
lean_dec_ref(v_recFnNames_3034_);
lean_dec_ref(v_positions_3033_);
lean_dec_ref(v_recArgInfos_3032_);
v_a_3099_ = lean_ctor_get(v___x_3097_, 0);
v___x_3100_ = l_Lean_Exception_isInterrupt(v_a_3099_);
if (v___x_3100_ == 0)
{
uint8_t v___x_3101_; 
lean_inc(v_a_3099_);
v___x_3101_ = l_Lean_Exception_isRuntime(v_a_3099_);
if (v___x_3101_ == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec_ref_known(v___x_3097_, 1);
v___x_3102_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3103_ = l_Lean_indentExpr(v_e_3037_);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3104_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
return v___x_3105_;
}
else
{
lean_dec_ref(v_e_3037_);
return v___x_3097_;
}
}
else
{
lean_dec_ref(v_e_3037_);
return v___x_3097_;
}
}
}
else
{
lean_dec(v_val_3056_);
lean_dec_ref(v_x_3039_);
lean_dec_ref(v_e_3037_);
lean_dec_ref(v_below_3036_);
lean_dec_ref(v_containsRecFn_3035_);
lean_dec_ref(v_recFnNames_3034_);
lean_dec_ref(v_positions_3033_);
lean_dec_ref(v_recArgInfos_3032_);
return v___x_3093_;
}
}
v___jp_3061_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v_snd_3065_; size_t v_sz_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3063_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3058_, v_x_3039_);
lean_dec_ref(v_x_3039_);
lean_inc(v___x_3057_);
v___x_3064_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3057_, v___x_3063_);
v_snd_3065_ = lean_ctor_get(v___x_3064_, 1);
lean_inc(v_snd_3065_);
lean_dec_ref(v___x_3064_);
v_sz_3066_ = lean_array_size(v_snd_3065_);
v___x_3067_ = ((size_t)0ULL);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3032_, v_positions_3033_, v_recFnNames_3034_, v_containsRecFn_3035_, v_below_3036_, v_sz_3066_, v___x_3067_, v_snd_3065_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3077_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3071_ = v___x_3068_;
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
else
{
lean_inc(v_a_3069_);
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3077_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = l_Lean_mkAppN(v_a_3062_, v_a_3069_);
lean_dec(v_a_3069_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 0, v___x_3073_);
v___x_3075_ = v___x_3071_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec_ref(v_a_3062_);
v_a_3078_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3068_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3068_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
}
else
{
lean_object* v___x_3106_; 
lean_dec(v___x_3055_);
lean_dec_ref(v_e_3037_);
lean_inc_ref(v___y_3044_);
lean_inc_ref(v_below_3036_);
lean_inc_ref(v_containsRecFn_3035_);
lean_inc_ref(v_recFnNames_3034_);
lean_inc_ref(v_positions_3033_);
lean_inc_ref(v_recArgInfos_3032_);
v___x_3106_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3032_, v_positions_3033_, v_recFnNames_3034_, v_containsRecFn_3035_, v_below_3036_, v_x_3038_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; size_t v_sz_3108_; size_t v___x_3109_; lean_object* v___x_3110_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
v_sz_3108_ = lean_array_size(v_x_3039_);
v___x_3109_ = ((size_t)0ULL);
v___x_3110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3032_, v_positions_3033_, v_recFnNames_3034_, v_containsRecFn_3035_, v_below_3036_, v_sz_3108_, v___x_3109_, v_x_3039_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3119_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3113_ = v___x_3110_;
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3110_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3119_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = l_Lean_mkAppN(v_a_3107_, v_a_3111_);
lean_dec(v_a_3111_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 0, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v_a_3107_);
v_a_3120_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3110_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3110_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_dec_ref(v_x_3039_);
lean_dec_ref(v_below_3036_);
lean_dec_ref(v_containsRecFn_3035_);
lean_dec_ref(v_recFnNames_3034_);
lean_dec_ref(v_positions_3033_);
lean_dec_ref(v_recArgInfos_3032_);
return v___x_3106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3128_, lean_object* v_recArgInfos_3129_, lean_object* v_positions_3130_, lean_object* v_recFnNames_3131_, lean_object* v_containsRecFn_3132_, lean_object* v_below_3133_, uint8_t v___x_3134_, uint8_t v_a_3135_, lean_object* v_x_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
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
v___x_3150_ = l_Lean_Meta_mkLambdaFVars(v___x_3148_, v_a_3145_, v___x_3134_, v_a_3135_, v___x_3134_, v_a_3135_, v___x_3149_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3151_, lean_object* v_recArgInfos_3152_, lean_object* v_positions_3153_, lean_object* v_recFnNames_3154_, lean_object* v_containsRecFn_3155_, lean_object* v_below_3156_, lean_object* v___x_3157_, lean_object* v_a_3158_, lean_object* v_x_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
uint8_t v___x_29249__boxed_3166_; uint8_t v_a_29250__boxed_3167_; lean_object* v_res_3168_; 
v___x_29249__boxed_3166_ = lean_unbox(v___x_3157_);
v_a_29250__boxed_3167_ = lean_unbox(v_a_3158_);
v_res_3168_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3151_, v_recArgInfos_3152_, v_positions_3153_, v_recFnNames_3154_, v_containsRecFn_3155_, v_below_3156_, v___x_29249__boxed_3166_, v_a_29250__boxed_3167_, v_x_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v_body_3151_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3169_, lean_object* v_recArgInfos_3170_, lean_object* v_positions_3171_, lean_object* v_recFnNames_3172_, lean_object* v_containsRecFn_3173_, lean_object* v_below_3174_, uint8_t v___x_3175_, uint8_t v_a_3176_, lean_object* v_x_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_expr_instantiate1(v_body_3169_, v_x_3177_);
lean_inc_ref(v___y_3181_);
v___x_3185_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3170_, v_positions_3171_, v_recFnNames_3172_, v_containsRecFn_3173_, v_below_3174_, v___x_3184_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; lean_object* v___x_3191_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = lean_unsigned_to_nat(1u);
v___x_3188_ = lean_mk_empty_array_with_capacity(v___x_3187_);
v___x_3189_ = lean_array_push(v___x_3188_, v_x_3177_);
v___x_3190_ = 1;
v___x_3191_ = l_Lean_Meta_mkForallFVars(v___x_3189_, v_a_3186_, v___x_3175_, v_a_3176_, v_a_3176_, v___x_3190_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec_ref(v___x_3189_);
return v___x_3191_;
}
else
{
lean_dec_ref(v_x_3177_);
return v___x_3185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3192_, lean_object* v_recArgInfos_3193_, lean_object* v_positions_3194_, lean_object* v_recFnNames_3195_, lean_object* v_containsRecFn_3196_, lean_object* v_below_3197_, lean_object* v___x_3198_, lean_object* v_a_3199_, lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
uint8_t v___x_29267__boxed_3207_; uint8_t v_a_29268__boxed_3208_; lean_object* v_res_3209_; 
v___x_29267__boxed_3207_ = lean_unbox(v___x_3198_);
v_a_29268__boxed_3208_ = lean_unbox(v_a_3199_);
v_res_3209_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3192_, v_recArgInfos_3193_, v_positions_3194_, v_recFnNames_3195_, v_containsRecFn_3196_, v_below_3197_, v___x_29267__boxed_3207_, v_a_29268__boxed_3208_, v_x_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v_body_3192_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3210_, lean_object* v_recArgInfos_3211_, lean_object* v_positions_3212_, lean_object* v_recFnNames_3213_, lean_object* v_containsRecFn_3214_, lean_object* v_below_3215_, lean_object* v_x_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3210_, v_recArgInfos_3211_, v_positions_3212_, v_recFnNames_3213_, v_containsRecFn_3214_, v_below_3215_, v_x_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v_x_3216_);
lean_dec_ref(v_body_3210_);
return v_res_3223_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3231_ = l_Lean_stringToMessageData(v___x_3230_);
return v___x_3231_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3234_ = l_Lean_stringToMessageData(v___x_3233_);
return v___x_3234_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3238_, lean_object* v_b_3239_, lean_object* v_recArgInfos_3240_, lean_object* v_positions_3241_, lean_object* v_recFnNames_3242_, lean_object* v_containsRecFn_3243_, uint8_t v___x_3244_, uint8_t v_a_3245_, lean_object* v___x_3246_, lean_object* v_a_3247_, lean_object* v_e_3248_, lean_object* v___x_3249_, lean_object* v_xs_3250_, lean_object* v_altBody_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v___y_3259_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v_toCold_3293_; lean_object* v_options_3294_; uint8_t v_hasTrace_3295_; 
v_toCold_3293_ = lean_ctor_get(v___y_3255_, 0);
v_options_3294_ = lean_ctor_get(v_toCold_3293_, 2);
v_hasTrace_3295_ = lean_ctor_get_uint8(v_options_3294_, sizeof(void*)*1);
if (v_hasTrace_3295_ == 0)
{
lean_dec(v___x_3249_);
v___y_3270_ = v___y_3252_;
v___y_3271_ = v___y_3253_;
v___y_3272_ = v___y_3254_;
v___y_3273_ = v___y_3255_;
v___y_3274_ = v___y_3256_;
goto v___jp_3269_;
}
else
{
lean_object* v_inheritedTraceOptions_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; uint8_t v___x_3299_; 
v_inheritedTraceOptions_3296_ = lean_ctor_get(v_toCold_3293_, 11);
v___x_3297_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3249_);
v___x_3298_ = l_Lean_Name_append(v___x_3297_, v___x_3249_);
v___x_3299_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3296_, v_options_3294_, v___x_3298_);
lean_dec(v___x_3298_);
if (v___x_3299_ == 0)
{
lean_dec(v___x_3249_);
v___y_3270_ = v___y_3252_;
v___y_3271_ = v___y_3253_;
v___y_3272_ = v___y_3254_;
v___y_3273_ = v___y_3255_;
v___y_3274_ = v___y_3256_;
goto v___jp_3269_;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3300_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3239_);
v___x_3301_ = l_Nat_reprFast(v_b_3239_);
v___x_3302_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v___x_3303_ = l_Lean_MessageData_ofFormat(v___x_3302_);
v___x_3304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3300_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
lean_inc_ref(v_xs_3250_);
v___x_3307_ = lean_array_to_list(v_xs_3250_);
v___x_3308_ = lean_box(0);
v___x_3309_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3307_, v___x_3308_);
v___x_3310_ = l_Lean_MessageData_ofList(v___x_3309_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3306_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3249_, v___x_3311_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
v___y_3270_ = v___y_3252_;
v___y_3271_ = v___y_3253_;
v___y_3272_ = v___y_3254_;
v___y_3273_ = v___y_3255_;
v___y_3274_ = v___y_3256_;
goto v___jp_3269_;
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref(v_altBody_3251_);
lean_dec_ref(v_xs_3250_);
lean_dec_ref(v_e_3248_);
lean_dec_ref(v_a_3247_);
lean_dec_ref(v_containsRecFn_3243_);
lean_dec_ref(v_recFnNames_3242_);
lean_dec_ref(v_positions_3241_);
lean_dec_ref(v_recArgInfos_3240_);
lean_dec(v_b_3239_);
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3312_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3312_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
}
v___jp_3258_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = lean_array_get_borrowed(v___x_3238_, v_xs_3250_, v_b_3239_);
lean_dec(v_b_3239_);
lean_inc_ref(v___y_3262_);
lean_inc(v___x_3264_);
v___x_3265_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3240_, v_positions_3241_, v_recFnNames_3242_, v_containsRecFn_3243_, v___x_3264_, v_altBody_3251_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; uint8_t v___x_3267_; lean_object* v___x_3268_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = 1;
v___x_3268_ = l_Lean_Meta_mkLambdaFVars(v_xs_3250_, v_a_3266_, v___x_3244_, v_a_3245_, v___x_3244_, v_a_3245_, v___x_3267_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
lean_dec_ref(v_xs_3250_);
return v___x_3268_;
}
else
{
lean_dec_ref(v_xs_3250_);
return v___x_3265_;
}
}
v___jp_3269_:
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = lean_array_get_size(v_xs_3250_);
v___x_3276_ = lean_nat_dec_eq(v___x_3275_, v___x_3246_);
if (v___x_3276_ == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v_altBody_3251_);
lean_dec_ref(v_xs_3250_);
lean_dec_ref(v_containsRecFn_3243_);
lean_dec_ref(v_recFnNames_3242_);
lean_dec_ref(v_positions_3241_);
lean_dec_ref(v_recArgInfos_3240_);
lean_dec(v_b_3239_);
v___x_3277_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3278_ = l_Lean_indentExpr(v_a_3247_);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_indentExpr(v_e_3248_);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3283_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_dec_ref(v_e_3248_);
lean_dec_ref(v_a_3247_);
v___y_3259_ = v___y_3270_;
v___y_3260_ = v___y_3271_;
v___y_3261_ = v___y_3272_;
v___y_3262_ = v___y_3273_;
v___y_3263_ = v___y_3274_;
goto v___jp_3258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3321_ = _args[0];
lean_object* v_b_3322_ = _args[1];
lean_object* v_recArgInfos_3323_ = _args[2];
lean_object* v_positions_3324_ = _args[3];
lean_object* v_recFnNames_3325_ = _args[4];
lean_object* v_containsRecFn_3326_ = _args[5];
lean_object* v___x_3327_ = _args[6];
lean_object* v_a_3328_ = _args[7];
lean_object* v___x_3329_ = _args[8];
lean_object* v_a_3330_ = _args[9];
lean_object* v_e_3331_ = _args[10];
lean_object* v___x_3332_ = _args[11];
lean_object* v_xs_3333_ = _args[12];
lean_object* v_altBody_3334_ = _args[13];
lean_object* v___y_3335_ = _args[14];
lean_object* v___y_3336_ = _args[15];
lean_object* v___y_3337_ = _args[16];
lean_object* v___y_3338_ = _args[17];
lean_object* v___y_3339_ = _args[18];
lean_object* v___y_3340_ = _args[19];
_start:
{
uint8_t v___x_29343__boxed_3341_; uint8_t v_a_29344__boxed_3342_; lean_object* v_res_3343_; 
v___x_29343__boxed_3341_ = lean_unbox(v___x_3327_);
v_a_29344__boxed_3342_ = lean_unbox(v_a_3328_);
v_res_3343_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3321_, v_b_3322_, v_recArgInfos_3323_, v_positions_3324_, v_recFnNames_3325_, v_containsRecFn_3326_, v___x_29343__boxed_3341_, v_a_29344__boxed_3342_, v___x_3329_, v_a_3330_, v_e_3331_, v___x_3332_, v_xs_3333_, v_altBody_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec(v___x_3329_);
lean_dec_ref(v___x_3321_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3344_, lean_object* v_positions_3345_, lean_object* v_recFnNames_3346_, lean_object* v_containsRecFn_3347_, uint8_t v_a_3348_, lean_object* v_e_3349_, lean_object* v_as_3350_, lean_object* v_bs_3351_, lean_object* v_i_3352_, lean_object* v_cs_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3360_ = lean_array_get_size(v_as_3350_);
v___x_3361_ = lean_nat_dec_lt(v_i_3352_, v___x_3360_);
if (v___x_3361_ == 0)
{
lean_object* v___x_3362_; 
lean_dec(v_i_3352_);
lean_dec_ref(v_e_3349_);
lean_dec_ref(v_containsRecFn_3347_);
lean_dec_ref(v_recFnNames_3346_);
lean_dec_ref(v_positions_3345_);
lean_dec_ref(v_recArgInfos_3344_);
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_cs_3353_);
return v___x_3362_;
}
else
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3363_ = lean_array_get_size(v_bs_3351_);
v___x_3364_ = lean_nat_dec_lt(v_i_3352_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_dec(v_i_3352_);
lean_dec_ref(v_e_3349_);
lean_dec_ref(v_containsRecFn_3347_);
lean_dec_ref(v_recFnNames_3346_);
lean_dec_ref(v_positions_3345_);
lean_dec_ref(v_recArgInfos_3344_);
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v_cs_3353_);
return v___x_3365_;
}
else
{
lean_object* v___x_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v_a_3369_; lean_object* v_b_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___f_3375_; lean_object* v___x_3376_; 
v___x_3366_ = l_Lean_instInhabitedExpr;
v___x_3367_ = 0;
v___x_3368_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3369_ = lean_array_fget_borrowed(v_as_3350_, v_i_3352_);
v_b_3370_ = lean_array_fget_borrowed(v_bs_3351_, v_i_3352_);
v___x_3371_ = lean_unsigned_to_nat(1u);
v___x_3372_ = lean_nat_add(v_b_3370_, v___x_3371_);
v___x_3373_ = lean_box(v___x_3367_);
v___x_3374_ = lean_box(v_a_3348_);
lean_inc_ref(v_e_3349_);
lean_inc_n(v_a_3369_, 2);
lean_inc(v___x_3372_);
lean_inc_ref(v_containsRecFn_3347_);
lean_inc_ref(v_recFnNames_3346_);
lean_inc_ref(v_positions_3345_);
lean_inc_ref(v_recArgInfos_3344_);
lean_inc(v_b_3370_);
v___f_3375_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3375_, 0, v___x_3366_);
lean_closure_set(v___f_3375_, 1, v_b_3370_);
lean_closure_set(v___f_3375_, 2, v_recArgInfos_3344_);
lean_closure_set(v___f_3375_, 3, v_positions_3345_);
lean_closure_set(v___f_3375_, 4, v_recFnNames_3346_);
lean_closure_set(v___f_3375_, 5, v_containsRecFn_3347_);
lean_closure_set(v___f_3375_, 6, v___x_3373_);
lean_closure_set(v___f_3375_, 7, v___x_3374_);
lean_closure_set(v___f_3375_, 8, v___x_3372_);
lean_closure_set(v___f_3375_, 9, v_a_3369_);
lean_closure_set(v___f_3375_, 10, v_e_3349_);
lean_closure_set(v___f_3375_, 11, v___x_3368_);
v___x_3376_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3369_, v___x_3372_, v___f_3375_, v___x_3367_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = lean_nat_add(v_i_3352_, v___x_3371_);
lean_dec(v_i_3352_);
v___x_3379_ = lean_array_push(v_cs_3353_, v_a_3377_);
v_i_3352_ = v___x_3378_;
v_cs_3353_ = v___x_3379_;
goto _start;
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec_ref(v_cs_3353_);
lean_dec(v_i_3352_);
lean_dec_ref(v_e_3349_);
lean_dec_ref(v_containsRecFn_3347_);
lean_dec_ref(v_recFnNames_3346_);
lean_dec_ref(v_positions_3345_);
lean_dec_ref(v_recArgInfos_3344_);
v_a_3381_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3376_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3376_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
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
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3394_ = l_Lean_stringToMessageData(v___x_3393_);
return v___x_3394_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3397_ = l_Lean_stringToMessageData(v___x_3396_);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3398_, lean_object* v_positions_3399_, lean_object* v_recFnNames_3400_, lean_object* v_containsRecFn_3401_, lean_object* v_below_3402_, lean_object* v_e_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_e_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___x_3423_; 
lean_inc_ref(v_containsRecFn_3401_);
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
lean_inc(v_a_3406_);
lean_inc_ref(v_a_3405_);
lean_inc(v_a_3404_);
lean_inc_ref(v_e_3403_);
v___x_3423_ = lean_apply_7(v_containsRecFn_3401_, v_e_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, lean_box(0));
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3650_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3426_ = v___x_3423_;
v_isShared_3427_ = v_isSharedCheck_3650_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3423_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3650_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
uint8_t v___x_3428_; 
v___x_3428_ = lean_unbox(v_a_3424_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3407_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 0, v_e_3403_);
v___x_3430_ = v___x_3426_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_e_3403_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
else
{
uint8_t v___x_3432_; 
lean_del_object(v___x_3426_);
v___x_3432_ = 0;
switch(lean_obj_tag(v_e_3403_))
{
case 6:
{
lean_object* v_binderName_3433_; lean_object* v_binderType_3434_; lean_object* v_body_3435_; uint8_t v_binderInfo_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; lean_object* v___x_3439_; 
v_binderName_3433_ = lean_ctor_get(v_e_3403_, 0);
lean_inc(v_binderName_3433_);
v_binderType_3434_ = lean_ctor_get(v_e_3403_, 1);
lean_inc_ref(v_binderType_3434_);
v_body_3435_ = lean_ctor_get(v_e_3403_, 2);
lean_inc_ref(v_body_3435_);
v_binderInfo_3436_ = lean_ctor_get_uint8(v_e_3403_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3403_, 3);
v___x_3437_ = lean_box(v___x_3432_);
lean_inc_ref(v_below_3402_);
lean_inc_ref(v_containsRecFn_3401_);
lean_inc_ref(v_recFnNames_3400_);
lean_inc_ref(v_positions_3399_);
lean_inc_ref(v_recArgInfos_3398_);
v___f_3438_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3438_, 0, v_body_3435_);
lean_closure_set(v___f_3438_, 1, v_recArgInfos_3398_);
lean_closure_set(v___f_3438_, 2, v_positions_3399_);
lean_closure_set(v___f_3438_, 3, v_recFnNames_3400_);
lean_closure_set(v___f_3438_, 4, v_containsRecFn_3401_);
lean_closure_set(v___f_3438_, 5, v_below_3402_);
lean_closure_set(v___f_3438_, 6, v___x_3437_);
lean_closure_set(v___f_3438_, 7, v_a_3424_);
lean_inc_ref(v_a_3407_);
v___x_3439_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_binderType_3434_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; uint8_t v___x_3441_; lean_object* v___x_3442_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = 0;
v___x_3442_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3433_, v_binderInfo_3436_, v_a_3440_, v___f_3438_, v___x_3441_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec_ref(v_a_3407_);
return v___x_3442_;
}
else
{
lean_dec_ref(v___f_3438_);
lean_dec(v_binderName_3433_);
lean_dec_ref(v_a_3407_);
return v___x_3439_;
}
}
case 7:
{
lean_object* v_binderName_3443_; lean_object* v_binderType_3444_; lean_object* v_body_3445_; uint8_t v_binderInfo_3446_; lean_object* v___x_3447_; lean_object* v___f_3448_; lean_object* v___x_3449_; 
v_binderName_3443_ = lean_ctor_get(v_e_3403_, 0);
lean_inc(v_binderName_3443_);
v_binderType_3444_ = lean_ctor_get(v_e_3403_, 1);
lean_inc_ref(v_binderType_3444_);
v_body_3445_ = lean_ctor_get(v_e_3403_, 2);
lean_inc_ref(v_body_3445_);
v_binderInfo_3446_ = lean_ctor_get_uint8(v_e_3403_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3403_, 3);
v___x_3447_ = lean_box(v___x_3432_);
lean_inc_ref(v_below_3402_);
lean_inc_ref(v_containsRecFn_3401_);
lean_inc_ref(v_recFnNames_3400_);
lean_inc_ref(v_positions_3399_);
lean_inc_ref(v_recArgInfos_3398_);
v___f_3448_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3448_, 0, v_body_3445_);
lean_closure_set(v___f_3448_, 1, v_recArgInfos_3398_);
lean_closure_set(v___f_3448_, 2, v_positions_3399_);
lean_closure_set(v___f_3448_, 3, v_recFnNames_3400_);
lean_closure_set(v___f_3448_, 4, v_containsRecFn_3401_);
lean_closure_set(v___f_3448_, 5, v_below_3402_);
lean_closure_set(v___f_3448_, 6, v___x_3447_);
lean_closure_set(v___f_3448_, 7, v_a_3424_);
lean_inc_ref(v_a_3407_);
v___x_3449_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_binderType_3444_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
v___x_3451_ = 0;
v___x_3452_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3443_, v_binderInfo_3446_, v_a_3450_, v___f_3448_, v___x_3451_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec_ref(v_a_3407_);
return v___x_3452_;
}
else
{
lean_dec_ref(v___f_3448_);
lean_dec(v_binderName_3443_);
lean_dec_ref(v_a_3407_);
return v___x_3449_;
}
}
case 8:
{
lean_object* v_declName_3453_; lean_object* v_type_3454_; lean_object* v_value_3455_; lean_object* v_body_3456_; uint8_t v_nondep_3457_; lean_object* v___f_3458_; lean_object* v___x_3459_; 
lean_dec(v_a_3424_);
v_declName_3453_ = lean_ctor_get(v_e_3403_, 0);
lean_inc(v_declName_3453_);
v_type_3454_ = lean_ctor_get(v_e_3403_, 1);
lean_inc_ref(v_type_3454_);
v_value_3455_ = lean_ctor_get(v_e_3403_, 2);
lean_inc_ref(v_value_3455_);
v_body_3456_ = lean_ctor_get(v_e_3403_, 3);
lean_inc_ref(v_body_3456_);
v_nondep_3457_ = lean_ctor_get_uint8(v_e_3403_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3403_, 4);
lean_inc_ref_n(v_below_3402_, 2);
lean_inc_ref_n(v_containsRecFn_3401_, 2);
lean_inc_ref_n(v_recFnNames_3400_, 2);
lean_inc_ref_n(v_positions_3399_, 2);
lean_inc_ref_n(v_recArgInfos_3398_, 2);
v___f_3458_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3458_, 0, v_body_3456_);
lean_closure_set(v___f_3458_, 1, v_recArgInfos_3398_);
lean_closure_set(v___f_3458_, 2, v_positions_3399_);
lean_closure_set(v___f_3458_, 3, v_recFnNames_3400_);
lean_closure_set(v___f_3458_, 4, v_containsRecFn_3401_);
lean_closure_set(v___f_3458_, 5, v_below_3402_);
lean_inc_ref(v_a_3407_);
v___x_3459_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_type_3454_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
lean_inc_ref(v_a_3407_);
v___x_3461_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_value_3455_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; uint8_t v___x_3463_; lean_object* v___x_3464_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = 0;
v___x_3464_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3453_, v_a_3460_, v_a_3462_, v___f_3458_, v_nondep_3457_, v___x_3463_, v___x_3432_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec_ref(v_a_3407_);
return v___x_3464_;
}
else
{
lean_dec(v_a_3460_);
lean_dec_ref(v___f_3458_);
lean_dec(v_declName_3453_);
lean_dec_ref(v_a_3407_);
return v___x_3461_;
}
}
else
{
lean_dec_ref(v___f_3458_);
lean_dec_ref(v_value_3455_);
lean_dec(v_declName_3453_);
lean_dec_ref(v_a_3407_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
return v___x_3459_;
}
}
case 10:
{
lean_object* v_data_3465_; lean_object* v_expr_3466_; lean_object* v___x_3467_; 
lean_dec(v_a_3424_);
v_data_3465_ = lean_ctor_get(v_e_3403_, 0);
lean_inc(v_data_3465_);
v_expr_3466_ = lean_ctor_get(v_e_3403_, 1);
lean_inc_ref(v_expr_3466_);
v___x_3467_ = l_Lean_getRecAppSyntax_x3f(v_e_3403_);
lean_dec_ref_known(v_e_3403_, 2);
if (lean_obj_tag(v___x_3467_) == 1)
{
lean_object* v_val_3468_; lean_object* v_toCold_3469_; lean_object* v_currRecDepth_3470_; lean_object* v_ref_3471_; uint16_t v_optionFlags_3472_; uint8_t v_suppressElabErrors_3473_; uint8_t v_checkDeprecated_3474_; uint8_t v_isRecordingDeps_3475_; lean_object* v_ref_3476_; lean_object* v___x_3477_; 
lean_dec(v_data_3465_);
v_val_3468_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_val_3468_);
lean_dec_ref_known(v___x_3467_, 1);
v_toCold_3469_ = lean_ctor_get(v_a_3407_, 0);
lean_inc_ref(v_toCold_3469_);
v_currRecDepth_3470_ = lean_ctor_get(v_a_3407_, 1);
lean_inc(v_currRecDepth_3470_);
v_ref_3471_ = lean_ctor_get(v_a_3407_, 2);
lean_inc(v_ref_3471_);
v_optionFlags_3472_ = lean_ctor_get_uint16(v_a_3407_, sizeof(void*)*3);
v_suppressElabErrors_3473_ = lean_ctor_get_uint8(v_a_3407_, sizeof(void*)*3 + 2);
v_checkDeprecated_3474_ = lean_ctor_get_uint8(v_a_3407_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3475_ = lean_ctor_get_uint8(v_a_3407_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_3407_);
v_ref_3476_ = l_Lean_replaceRef(v_val_3468_, v_ref_3471_);
lean_dec(v_ref_3471_);
lean_dec(v_val_3468_);
v___x_3477_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3477_, 0, v_toCold_3469_);
lean_ctor_set(v___x_3477_, 1, v_currRecDepth_3470_);
lean_ctor_set(v___x_3477_, 2, v_ref_3476_);
lean_ctor_set_uint16(v___x_3477_, sizeof(void*)*3, v_optionFlags_3472_);
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*3 + 2, v_suppressElabErrors_3473_);
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*3 + 3, v_checkDeprecated_3474_);
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*3 + 4, v_isRecordingDeps_3475_);
v_e_3403_ = v_expr_3466_;
v_a_3407_ = v___x_3477_;
goto _start;
}
else
{
lean_object* v___x_3479_; 
lean_dec(v___x_3467_);
v___x_3479_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_expr_3466_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3488_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = l_Lean_mkMData(v_data_3465_, v_a_3480_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3484_);
v___x_3486_ = v___x_3482_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
else
{
lean_dec(v_data_3465_);
return v___x_3479_;
}
}
}
case 11:
{
lean_object* v_typeName_3489_; lean_object* v_idx_3490_; lean_object* v_struct_3491_; lean_object* v___x_3492_; 
lean_dec(v_a_3424_);
v_typeName_3489_ = lean_ctor_get(v_e_3403_, 0);
lean_inc(v_typeName_3489_);
v_idx_3490_ = lean_ctor_get(v_e_3403_, 1);
lean_inc(v_idx_3490_);
v_struct_3491_ = lean_ctor_get(v_e_3403_, 2);
lean_inc_ref(v_struct_3491_);
lean_dec_ref_known(v_e_3403_, 3);
v___x_3492_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_struct_3491_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3501_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3501_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3501_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3497_ = l_Lean_mkProj(v_typeName_3489_, v_idx_3490_, v_a_3493_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3497_);
v___x_3499_ = v___x_3495_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
else
{
lean_dec(v_idx_3490_);
lean_dec(v_typeName_3489_);
return v___x_3492_;
}
}
case 5:
{
uint8_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = lean_unbox(v_a_3424_);
lean_inc_ref(v_e_3403_);
v___x_3503_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3403_, v___x_3502_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
if (lean_obj_tag(v_a_3504_) == 0)
{
lean_dec(v_a_3424_);
v_e_3411_ = v_e_3403_;
v___y_3412_ = v_a_3404_;
v___y_3413_ = v_a_3405_;
v___y_3414_ = v_a_3406_;
v___y_3415_ = v_a_3407_;
v___y_3416_ = v_a_3408_;
goto v___jp_3410_;
}
else
{
lean_object* v_val_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v_val_3505_ = lean_ctor_get(v_a_3504_, 0);
lean_inc(v_val_3505_);
lean_dec_ref_known(v_a_3504_, 1);
v___x_3506_ = lean_unsigned_to_nat(0u);
v___x_3507_ = lean_array_get_size(v_recArgInfos_3398_);
v___x_3508_ = lean_nat_dec_lt(v___x_3506_, v___x_3507_);
if (v___x_3508_ == 0)
{
lean_dec(v_val_3505_);
lean_dec(v_a_3424_);
v_e_3411_ = v_e_3403_;
v___y_3412_ = v_a_3404_;
v___y_3413_ = v_a_3405_;
v___y_3414_ = v_a_3406_;
v___y_3415_ = v_a_3407_;
v___y_3416_ = v_a_3408_;
goto v___jp_3410_;
}
else
{
if (v___x_3508_ == 0)
{
lean_dec(v_val_3505_);
lean_dec(v_a_3424_);
v_e_3411_ = v_e_3403_;
v___y_3412_ = v_a_3404_;
v___y_3413_ = v_a_3405_;
v___y_3414_ = v_a_3406_;
v___y_3415_ = v_a_3407_;
v___y_3416_ = v_a_3408_;
goto v___jp_3410_;
}
else
{
size_t v___x_3509_; size_t v___x_3510_; uint8_t v___x_3511_; 
v___x_3509_ = ((size_t)0ULL);
v___x_3510_ = lean_usize_of_nat(v___x_3507_);
v___x_3511_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3403_, v_recArgInfos_3398_, v___x_3509_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_dec(v_val_3505_);
lean_dec(v_a_3424_);
v_e_3411_ = v_e_3403_;
v___y_3412_ = v_a_3404_;
v___y_3413_ = v_a_3405_;
v___y_3414_ = v_a_3406_;
v___y_3415_ = v_a_3407_;
v___y_3416_ = v_a_3408_;
goto v___jp_3410_;
}
else
{
lean_object* v_toCold_3512_; lean_object* v_inheritedTraceOptions_3513_; lean_object* v___x_3514_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___x_3596_; 
v_toCold_3512_ = lean_ctor_get(v_a_3407_, 0);
v_inheritedTraceOptions_3513_ = lean_ctor_get(v_toCold_3512_, 11);
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3596_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3514_, v_inheritedTraceOptions_3513_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; uint8_t v___x_3598_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v___x_3598_ = lean_unbox(v_a_3597_);
lean_dec(v_a_3597_);
if (v___x_3598_ == 0)
{
v___y_3516_ = v_a_3404_;
v___y_3517_ = v_a_3405_;
v___y_3518_ = v_a_3406_;
v___y_3519_ = v_a_3407_;
v___y_3520_ = v_a_3408_;
goto v___jp_3515_;
}
else
{
lean_object* v___x_3599_; 
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
lean_inc(v_a_3406_);
lean_inc_ref(v_a_3405_);
lean_inc_ref(v_below_3402_);
v___x_3599_ = lean_infer_type(v_below_3402_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3402_);
v___x_3602_ = l_Lean_MessageData_ofExpr(v_below_3402_);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = l_Lean_MessageData_ofExpr(v_a_3600_);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3514_, v___x_3607_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_dec_ref_known(v___x_3608_, 1);
v___y_3516_ = v_a_3404_;
v___y_3517_ = v_a_3405_;
v___y_3518_ = v_a_3406_;
v___y_3519_ = v_a_3407_;
v___y_3520_ = v_a_3408_;
goto v___jp_3515_;
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_val_3505_);
lean_dec_ref_known(v_e_3403_, 2);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3407_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
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
else
{
lean_dec(v_val_3505_);
lean_dec_ref_known(v_e_3403_, 2);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3407_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
return v___x_3599_;
}
}
}
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec(v_val_3505_);
lean_dec_ref_known(v_e_3403_, 2);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3407_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
v_a_3617_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3596_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3596_);
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
v___jp_3515_:
{
lean_object* v___x_3521_; 
lean_inc_ref(v_below_3402_);
v___x_3521_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3505_, v_below_3402_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_val_3523_; lean_object* v_toMatcherInfo_3524_; lean_object* v_matcherName_3525_; lean_object* v_matcherLevels_3526_; lean_object* v_params_3527_; lean_object* v_motive_3528_; lean_object* v_discrs_3529_; lean_object* v_alts_3530_; lean_object* v_remaining_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; lean_object* v___x_3535_; 
v_val_3523_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_val_3523_);
lean_dec_ref_known(v_a_3522_, 1);
v_toMatcherInfo_3524_ = lean_ctor_get(v_val_3523_, 0);
lean_inc_ref(v_toMatcherInfo_3524_);
v_matcherName_3525_ = lean_ctor_get(v_val_3523_, 1);
lean_inc(v_matcherName_3525_);
v_matcherLevels_3526_ = lean_ctor_get(v_val_3523_, 2);
lean_inc_ref(v_matcherLevels_3526_);
v_params_3527_ = lean_ctor_get(v_val_3523_, 3);
lean_inc_ref(v_params_3527_);
v_motive_3528_ = lean_ctor_get(v_val_3523_, 4);
lean_inc_ref(v_motive_3528_);
v_discrs_3529_ = lean_ctor_get(v_val_3523_, 5);
lean_inc_ref(v_discrs_3529_);
v_alts_3530_ = lean_ctor_get(v_val_3523_, 6);
lean_inc_ref(v_alts_3530_);
v_remaining_3531_ = lean_ctor_get(v_val_3523_, 7);
lean_inc_ref(v_remaining_3531_);
v___x_3532_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3523_);
v___x_3533_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3534_ = lean_unbox(v_a_3424_);
lean_dec(v_a_3424_);
lean_inc_ref(v_containsRecFn_3401_);
lean_inc_ref(v_recFnNames_3400_);
lean_inc_ref(v_positions_3399_);
lean_inc_ref(v_recArgInfos_3398_);
v___x_3535_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v___x_3534_, v_e_3403_, v_alts_3530_, v___x_3532_, v___x_3506_, v___x_3533_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec_ref(v___x_3532_);
lean_dec_ref(v_alts_3530_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; size_t v_sz_3537_; lean_object* v___x_3538_; 
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v_sz_3537_ = lean_array_size(v_discrs_3529_);
v___x_3538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_sz_3537_, v___x_3509_, v_discrs_3529_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec_ref(v___y_3519_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3548_; 
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3548_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3548_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3543_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3543_, 0, v_toMatcherInfo_3524_);
lean_ctor_set(v___x_3543_, 1, v_matcherName_3525_);
lean_ctor_set(v___x_3543_, 2, v_matcherLevels_3526_);
lean_ctor_set(v___x_3543_, 3, v_params_3527_);
lean_ctor_set(v___x_3543_, 4, v_motive_3528_);
lean_ctor_set(v___x_3543_, 5, v_a_3539_);
lean_ctor_set(v___x_3543_, 6, v_a_3536_);
lean_ctor_set(v___x_3543_, 7, v_remaining_3531_);
v___x_3544_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3543_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 0, v___x_3544_);
v___x_3546_ = v___x_3541_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec(v_a_3536_);
lean_dec_ref(v_remaining_3531_);
lean_dec_ref(v_motive_3528_);
lean_dec_ref(v_params_3527_);
lean_dec_ref(v_matcherLevels_3526_);
lean_dec(v_matcherName_3525_);
lean_dec_ref(v_toMatcherInfo_3524_);
v_a_3549_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3538_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3538_);
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
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_dec_ref(v_remaining_3531_);
lean_dec_ref(v_discrs_3529_);
lean_dec_ref(v_motive_3528_);
lean_dec_ref(v_params_3527_);
lean_dec_ref(v_matcherLevels_3526_);
lean_dec(v_matcherName_3525_);
lean_dec_ref(v_toMatcherInfo_3524_);
lean_dec_ref(v___y_3519_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
v_a_3557_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3535_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3535_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
else
{
lean_object* v_toCold_3565_; lean_object* v_inheritedTraceOptions_3566_; lean_object* v___x_3567_; 
lean_dec(v_a_3522_);
lean_dec(v_a_3424_);
v_toCold_3565_ = lean_ctor_get(v___y_3519_, 0);
v_inheritedTraceOptions_3566_ = lean_ctor_get(v_toCold_3565_, 11);
v___x_3567_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3514_, v_inheritedTraceOptions_3566_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; uint8_t v___x_3569_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = lean_unbox(v_a_3568_);
lean_dec(v_a_3568_);
if (v___x_3569_ == 0)
{
v_e_3411_ = v_e_3403_;
v___y_3412_ = v___y_3516_;
v___y_3413_ = v___y_3517_;
v___y_3414_ = v___y_3518_;
v___y_3415_ = v___y_3519_;
v___y_3416_ = v___y_3520_;
goto v___jp_3410_;
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3571_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3514_, v___x_3570_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_dec_ref_known(v___x_3571_, 1);
v_e_3411_ = v_e_3403_;
v___y_3412_ = v___y_3516_;
v___y_3413_ = v___y_3517_;
v___y_3414_ = v___y_3518_;
v___y_3415_ = v___y_3519_;
v___y_3416_ = v___y_3520_;
goto v___jp_3410_;
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec_ref(v___y_3519_);
lean_dec_ref_known(v_e_3403_, 2);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
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
}
else
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
lean_dec_ref(v___y_3519_);
lean_dec_ref_known(v_e_3403_, 2);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
v_a_3580_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3567_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3567_);
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
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v___y_3519_);
lean_dec_ref_known(v_e_3403_, 2);
lean_dec(v_a_3424_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
v_a_3588_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3521_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3521_);
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
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref_known(v_e_3403_, 2);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3407_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
v_a_3625_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3503_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3503_);
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
default: 
{
lean_object* v___x_3633_; 
lean_dec(v_a_3424_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
lean_inc_ref(v_e_3403_);
v___x_3633_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3400_, v_e_3403_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
lean_dec_ref(v_a_3407_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v___x_3633_, 0);
lean_dec(v_unused_3641_);
v___x_3635_ = v___x_3633_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_dec(v___x_3633_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v_e_3403_);
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_e_3403_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_e_3403_);
v_a_3642_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3633_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3633_);
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
}
}
}
}
else
{
lean_object* v_a_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3658_; 
lean_dec_ref(v_a_3407_);
lean_dec_ref(v_e_3403_);
lean_dec_ref(v_below_3402_);
lean_dec_ref(v_containsRecFn_3401_);
lean_dec_ref(v_recFnNames_3400_);
lean_dec_ref(v_positions_3399_);
lean_dec_ref(v_recArgInfos_3398_);
v_a_3651_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3653_ = v___x_3423_;
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_a_3651_);
lean_dec(v___x_3423_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3658_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3656_; 
if (v_isShared_3654_ == 0)
{
v___x_3656_ = v___x_3653_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
v___jp_3410_:
{
lean_object* v_dummy_3417_; lean_object* v_nargs_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_dummy_3417_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3418_ = l_Lean_Expr_getAppNumArgs(v_e_3411_);
lean_inc(v_nargs_3418_);
v___x_3419_ = lean_mk_array(v_nargs_3418_, v_dummy_3417_);
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_sub(v_nargs_3418_, v___x_3420_);
lean_dec(v_nargs_3418_);
lean_inc_ref(v_e_3411_);
v___x_3422_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3398_, v_positions_3399_, v_recFnNames_3400_, v_containsRecFn_3401_, v_below_3402_, v_e_3411_, v_e_3411_, v___x_3419_, v___x_3421_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec_ref(v___y_3415_);
return v___x_3422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3659_, lean_object* v_recArgInfos_3660_, lean_object* v_positions_3661_, lean_object* v_recFnNames_3662_, lean_object* v_containsRecFn_3663_, lean_object* v_below_3664_, lean_object* v_x_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = lean_expr_instantiate1(v_body_3659_, v_x_3665_);
lean_inc_ref(v___y_3669_);
v___x_3673_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3660_, v_positions_3661_, v_recFnNames_3662_, v_containsRecFn_3663_, v_below_3664_, v___x_3672_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3674_, lean_object* v_positions_3675_, lean_object* v_recFnNames_3676_, lean_object* v_containsRecFn_3677_, lean_object* v_below_3678_, lean_object* v_sz_3679_, lean_object* v_i_3680_, lean_object* v_bs_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
size_t v_sz_boxed_3688_; size_t v_i_boxed_3689_; lean_object* v_res_3690_; 
v_sz_boxed_3688_ = lean_unbox_usize(v_sz_3679_);
lean_dec(v_sz_3679_);
v_i_boxed_3689_ = lean_unbox_usize(v_i_3680_);
lean_dec(v_i_3680_);
v_res_3690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3674_, v_positions_3675_, v_recFnNames_3676_, v_containsRecFn_3677_, v_below_3678_, v_sz_boxed_3688_, v_i_boxed_3689_, v_bs_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_, v___y_3686_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3691_, lean_object* v_positions_3692_, lean_object* v_recFnNames_3693_, lean_object* v_containsRecFn_3694_, lean_object* v_a_3695_, lean_object* v_e_3696_, lean_object* v_as_3697_, lean_object* v_bs_3698_, lean_object* v_i_3699_, lean_object* v_cs_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v_a_29301__boxed_3707_; lean_object* v_res_3708_; 
v_a_29301__boxed_3707_ = lean_unbox(v_a_3695_);
v_res_3708_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3691_, v_positions_3692_, v_recFnNames_3693_, v_containsRecFn_3694_, v_a_29301__boxed_3707_, v_e_3696_, v_as_3697_, v_bs_3698_, v_i_3699_, v_cs_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v_bs_3698_);
lean_dec_ref(v_as_3697_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3709_, lean_object* v_positions_3710_, lean_object* v_recFnNames_3711_, lean_object* v_containsRecFn_3712_, lean_object* v_below_3713_, lean_object* v_e_3714_, lean_object* v_x_3715_, lean_object* v_x_3716_, lean_object* v_x_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3709_, v_positions_3710_, v_recFnNames_3711_, v_containsRecFn_3712_, v_below_3713_, v_e_3714_, v_x_3715_, v_x_3716_, v_x_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3725_, lean_object* v_positions_3726_, lean_object* v_recFnNames_3727_, lean_object* v_containsRecFn_3728_, lean_object* v_below_3729_, lean_object* v_e_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3725_, v_positions_3726_, v_recFnNames_3727_, v_containsRecFn_3728_, v_below_3729_, v_e_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3735_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3738_, lean_object* v_msg_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3739_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3747_, lean_object* v_msg_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3747_, v_msg_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3756_, lean_object* v_name_3757_, lean_object* v_type_3758_, lean_object* v_val_3759_, lean_object* v_k_3760_, uint8_t v_nondep_3761_, uint8_t v_kind_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3757_, v_type_3758_, v_val_3759_, v_k_3760_, v_nondep_3761_, v_kind_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
return v___x_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3770_, lean_object* v_name_3771_, lean_object* v_type_3772_, lean_object* v_val_3773_, lean_object* v_k_3774_, lean_object* v_nondep_3775_, lean_object* v_kind_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
uint8_t v_nondep_boxed_3783_; uint8_t v_kind_boxed_3784_; lean_object* v_res_3785_; 
v_nondep_boxed_3783_ = lean_unbox(v_nondep_3775_);
v_kind_boxed_3784_ = lean_unbox(v_kind_3776_);
v_res_3785_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3770_, v_name_3771_, v_type_3772_, v_val_3773_, v_k_3774_, v_nondep_boxed_3783_, v_kind_boxed_3784_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3786_, v___y_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3802_, lean_object* v_msg_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v___x_3810_; 
v___x_3810_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3802_, v_msg_3803_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_);
return v___x_3810_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3811_, lean_object* v_msg_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
lean_object* v_res_3819_; 
v_res_3819_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3811_, v_msg_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
return v_res_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3820_, lean_object* v_constName_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3829_, lean_object* v_constName_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3829_, v_constName_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3838_, lean_object* v_ref_3839_, lean_object* v_constName_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3839_, v_constName_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3848_, lean_object* v_ref_3849_, lean_object* v_constName_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3848_, v_ref_3849_, v_constName_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec(v_ref_3849_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3858_, lean_object* v_ref_3859_, lean_object* v_msg_3860_, lean_object* v_declHint_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3859_, v_msg_3860_, v_declHint_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3869_, lean_object* v_ref_3870_, lean_object* v_msg_3871_, lean_object* v_declHint_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3869_, v_ref_3870_, v_msg_3871_, v_declHint_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec(v_ref_3870_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3880_, lean_object* v_declHint_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3880_, v_declHint_3881_, v___y_3886_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3889_, lean_object* v_declHint_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3889_, v_declHint_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3898_, lean_object* v_ref_3899_, lean_object* v_msg_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3899_, v_msg_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3908_, lean_object* v_ref_3909_, lean_object* v_msg_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3908_, v_ref_3909_, v_msg_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec(v_ref_3909_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3918_, lean_object* v_e_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v_fst_3928_; lean_object* v_snd_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3926_ = lean_st_ref_take(v___y_3920_);
v___x_3927_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3918_, v_e_3919_, v___x_3926_);
v_fst_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_fst_3928_);
v_snd_3929_ = lean_ctor_get(v___x_3927_, 1);
lean_inc(v_snd_3929_);
lean_dec_ref(v___x_3927_);
v___x_3930_ = lean_st_ref_put(v___y_3920_, v_snd_3929_);
v___x_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3931_, 0, v_fst_3928_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3932_, lean_object* v_e_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3932_, v_e_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v_recFnNames_3932_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3941_, size_t v_i_3942_, lean_object* v_bs_3943_){
_start:
{
uint8_t v___x_3944_; 
v___x_3944_ = lean_usize_dec_lt(v_i_3942_, v_sz_3941_);
if (v___x_3944_ == 0)
{
return v_bs_3943_;
}
else
{
lean_object* v_v_3945_; lean_object* v_fnName_3946_; lean_object* v___x_3947_; lean_object* v_bs_x27_3948_; size_t v___x_3949_; size_t v___x_3950_; lean_object* v___x_3951_; 
v_v_3945_ = lean_array_uget_borrowed(v_bs_3943_, v_i_3942_);
v_fnName_3946_ = lean_ctor_get(v_v_3945_, 0);
lean_inc(v_fnName_3946_);
v___x_3947_ = lean_unsigned_to_nat(0u);
v_bs_x27_3948_ = lean_array_uset(v_bs_3943_, v_i_3942_, v___x_3947_);
v___x_3949_ = ((size_t)1ULL);
v___x_3950_ = lean_usize_add(v_i_3942_, v___x_3949_);
v___x_3951_ = lean_array_uset(v_bs_x27_3948_, v_i_3942_, v_fnName_3946_);
v_i_3942_ = v___x_3950_;
v_bs_3943_ = v___x_3951_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3953_, lean_object* v_i_3954_, lean_object* v_bs_3955_){
_start:
{
size_t v_sz_boxed_3956_; size_t v_i_boxed_3957_; lean_object* v_res_3958_; 
v_sz_boxed_3956_ = lean_unbox_usize(v_sz_3953_);
lean_dec(v_sz_3953_);
v_i_boxed_3957_ = lean_unbox_usize(v_i_3954_);
lean_dec(v_i_3954_);
v_res_3958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3956_, v_i_boxed_3957_, v_bs_3955_);
return v_res_3958_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = lean_box(0);
v___x_3960_ = lean_unsigned_to_nat(16u);
v___x_3961_ = lean_mk_array(v___x_3960_, v___x_3959_);
return v___x_3961_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3962_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3963_ = lean_unsigned_to_nat(0u);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
lean_ctor_set(v___x_3964_, 1, v___x_3962_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3965_, lean_object* v_positions_3966_, lean_object* v_below_3967_, lean_object* v_e_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_){
_start:
{
size_t v_sz_3974_; size_t v___x_3975_; lean_object* v_recFnNames_3976_; lean_object* v_containsRecFn_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v_sz_3974_ = lean_array_size(v_recArgInfos_3965_);
v___x_3975_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3965_);
v_recFnNames_3976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3974_, v___x_3975_, v_recArgInfos_3965_);
lean_inc_ref(v_recFnNames_3976_);
v_containsRecFn_3977_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3977_, 0, v_recFnNames_3976_);
v___x_3978_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3979_ = lean_st_mk_ref(v___x_3978_);
lean_inc_ref(v_a_3971_);
v___x_3980_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3965_, v_positions_3966_, v_recFnNames_3976_, v_containsRecFn_3977_, v_below_3967_, v_e_3968_, v___x_3979_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3989_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3989_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3985_ = lean_st_ref_get(v___x_3979_);
lean_dec(v___x_3979_);
lean_dec(v___x_3985_);
if (v_isShared_3984_ == 0)
{
v___x_3987_ = v___x_3983_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3981_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
else
{
lean_dec(v___x_3979_);
return v___x_3980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_3990_, lean_object* v_positions_3991_, lean_object* v_below_3992_, lean_object* v_e_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_3990_, v_positions_3991_, v_below_3992_, v_e_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4000_, lean_object* v_k_4001_, uint8_t v_cleanupAnnotations_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___f_4008_; uint8_t v___x_4009_; uint8_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___f_4008_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4008_, 0, v_k_4001_);
v___x_4009_ = 1;
v___x_4010_ = 0;
v___x_4011_ = lean_box(0);
v___x_4012_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4000_, v___x_4009_, v___x_4010_, v___x_4009_, v___x_4010_, v___x_4011_, v___f_4008_, v_cleanupAnnotations_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_4012_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_4012_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
v_a_4021_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4012_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4012_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4029_, lean_object* v_k_4030_, lean_object* v_cleanupAnnotations_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4037_; lean_object* v_res_4038_; 
v_cleanupAnnotations_boxed_4037_ = lean_unbox(v_cleanupAnnotations_4031_);
v_res_4038_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4029_, v_k_4030_, v_cleanupAnnotations_boxed_4037_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
return v_res_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4039_, lean_object* v_e_4040_, lean_object* v_k_4041_, uint8_t v_cleanupAnnotations_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4040_, v_k_4041_, v_cleanupAnnotations_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4049_, lean_object* v_e_4050_, lean_object* v_k_4051_, lean_object* v_cleanupAnnotations_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4058_; lean_object* v_res_4059_; 
v_cleanupAnnotations_boxed_4058_ = lean_unbox(v_cleanupAnnotations_4052_);
v_res_4059_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4049_, v_e_4050_, v_k_4051_, v_cleanupAnnotations_boxed_4058_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
lean_dec(v___y_4056_);
lean_dec_ref(v___y_4055_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
return v_res_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4060_, lean_object* v_recArgInfo_4061_, lean_object* v_xs_4062_, lean_object* v___value_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_Meta_instantiateForall(v_type_4060_, v_xs_4062_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4071_; lean_object* v_fst_4072_; lean_object* v_snd_4073_; uint8_t v___x_4074_; uint8_t v___x_4075_; uint8_t v___x_4076_; lean_object* v___x_4077_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v___x_4071_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4061_, v_xs_4062_);
v_fst_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_fst_4072_);
v_snd_4073_ = lean_ctor_get(v___x_4071_, 1);
lean_inc(v_snd_4073_);
lean_dec_ref(v___x_4071_);
v___x_4074_ = 0;
v___x_4075_ = 1;
v___x_4076_ = 1;
v___x_4077_ = l_Lean_Meta_mkForallFVars(v_snd_4073_, v_a_4070_, v___x_4074_, v___x_4075_, v___x_4075_, v___x_4076_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec(v_snd_4073_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
v___x_4079_ = l_Lean_Meta_mkLambdaFVars(v_fst_4072_, v_a_4078_, v___x_4074_, v___x_4075_, v___x_4074_, v___x_4075_, v___x_4076_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
lean_dec(v_fst_4072_);
return v___x_4079_;
}
else
{
lean_dec(v_fst_4072_);
return v___x_4077_;
}
}
else
{
lean_dec_ref(v_xs_4062_);
lean_dec_ref(v_recArgInfo_4061_);
return v___x_4069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4080_, lean_object* v_recArgInfo_4081_, lean_object* v_xs_4082_, lean_object* v___value_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4080_, v_recArgInfo_4081_, v_xs_4082_, v___value_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec_ref(v___value_4083_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4090_, lean_object* v_value_4091_, lean_object* v_type_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v___f_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; 
v___f_4098_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4098_, 0, v_type_4092_);
lean_closure_set(v___f_4098_, 1, v_recArgInfo_4090_);
v___x_4099_ = 0;
v___x_4100_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4091_, v___f_4098_, v___x_4099_, v_a_4093_, v_a_4094_, v_a_4095_, v_a_4096_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4101_, lean_object* v_value_4102_, lean_object* v_type_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4101_, v_value_4102_, v_type_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v_recArgInfos_4110_, lean_object* v_positions_4111_, lean_object* v_value_4112_, lean_object* v_fst_4113_, lean_object* v_snd_4114_, lean_object* v_below_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v___x_4121_; 
lean_inc_ref(v_below_4115_);
v___x_4121_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4110_, v_positions_4111_, v_below_4115_, v_value_4112_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4121_) == 0)
{
lean_object* v_a_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; uint8_t v___x_4129_; uint8_t v___x_4130_; lean_object* v___x_4131_; 
v_a_4122_ = lean_ctor_get(v___x_4121_, 0);
lean_inc(v_a_4122_);
lean_dec_ref_known(v___x_4121_, 1);
v___x_4123_ = lean_unsigned_to_nat(1u);
v___x_4124_ = lean_mk_empty_array_with_capacity(v___x_4123_);
v___x_4125_ = lean_array_push(v___x_4124_, v_below_4115_);
v___x_4126_ = l_Array_append___redArg(v_fst_4113_, v___x_4125_);
lean_dec_ref(v___x_4125_);
v___x_4127_ = l_Array_append___redArg(v___x_4126_, v_snd_4114_);
v___x_4128_ = 0;
v___x_4129_ = 1;
v___x_4130_ = 1;
v___x_4131_ = l_Lean_Meta_mkLambdaFVars(v___x_4127_, v_a_4122_, v___x_4128_, v___x_4129_, v___x_4128_, v___x_4129_, v___x_4130_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec_ref(v___x_4127_);
return v___x_4131_;
}
else
{
lean_dec_ref(v_below_4115_);
lean_dec_ref(v_fst_4113_);
return v___x_4121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v_recArgInfos_4132_, lean_object* v_positions_4133_, lean_object* v_value_4134_, lean_object* v_fst_4135_, lean_object* v_snd_4136_, lean_object* v_below_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v_recArgInfos_4132_, v_positions_4133_, v_value_4134_, v_fst_4135_, v_snd_4136_, v_below_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec_ref(v_snd_4136_);
return v_res_4143_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4146_ = l_Lean_stringToMessageData(v___x_4145_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4147_, lean_object* v_recArgInfos_4148_, lean_object* v_positions_4149_, lean_object* v_FType_4150_, lean_object* v_xs_4151_, lean_object* v_value_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v_fst_4159_; lean_object* v_snd_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4179_; 
v___x_4158_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4147_, v_xs_4151_);
v_fst_4159_ = lean_ctor_get(v___x_4158_, 0);
v_snd_4160_ = lean_ctor_get(v___x_4158_, 1);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4162_ = v___x_4158_;
v_isShared_4163_ = v_isSharedCheck_4179_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_snd_4160_);
lean_inc(v_fst_4159_);
lean_dec(v___x_4158_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4179_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___f_4164_; lean_object* v___x_4165_; 
lean_inc(v_fst_4159_);
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4164_, 0, v_recArgInfos_4148_);
lean_closure_set(v___f_4164_, 1, v_positions_4149_);
lean_closure_set(v___f_4164_, 2, v_value_4152_);
lean_closure_set(v___f_4164_, 3, v_fst_4159_);
lean_closure_set(v___f_4164_, 4, v_snd_4160_);
v___x_4165_ = l_Lean_Meta_instantiateForall(v_FType_4150_, v_fst_4159_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
lean_dec(v_fst_4159_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4167_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc_n(v_a_4166_, 2);
lean_dec_ref_known(v___x_4165_, 1);
v___x_4167_ = l_Lean_Meta_whnfForall(v_a_4166_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4167_, 1);
if (lean_obj_tag(v_a_4168_) == 7)
{
lean_object* v_binderName_4169_; lean_object* v_binderType_4170_; uint8_t v_binderInfo_4171_; lean_object* v___x_4172_; 
lean_dec(v_a_4166_);
lean_del_object(v___x_4162_);
v_binderName_4169_ = lean_ctor_get(v_a_4168_, 0);
lean_inc(v_binderName_4169_);
v_binderType_4170_ = lean_ctor_get(v_a_4168_, 1);
lean_inc_ref(v_binderType_4170_);
v_binderInfo_4171_ = lean_ctor_get_uint8(v_a_4168_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4168_, 3);
v___x_4172_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4169_, v_binderInfo_4171_, v_binderType_4170_, v___f_4164_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4172_;
}
else
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4176_; 
lean_dec(v_a_4168_);
lean_dec_ref(v___f_4164_);
v___x_4173_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1, &l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1);
v___x_4174_ = l_Lean_indentExpr(v_a_4166_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set_tag(v___x_4162_, 7);
lean_ctor_set(v___x_4162_, 1, v___x_4174_);
lean_ctor_set(v___x_4162_, 0, v___x_4173_);
v___x_4176_ = v___x_4162_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4173_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4176_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4177_;
}
}
}
else
{
lean_dec(v_a_4166_);
lean_dec_ref(v___f_4164_);
lean_del_object(v___x_4162_);
return v___x_4167_;
}
}
else
{
lean_dec_ref(v___f_4164_);
lean_del_object(v___x_4162_);
return v___x_4165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4180_, lean_object* v_recArgInfos_4181_, lean_object* v_positions_4182_, lean_object* v_FType_4183_, lean_object* v_xs_4184_, lean_object* v_value_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4180_, v_recArgInfos_4181_, v_positions_4182_, v_FType_4183_, v_xs_4184_, v_value_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4192_, lean_object* v_positions_4193_, lean_object* v_recArgInfo_4194_, lean_object* v_value_4195_, lean_object* v_FType_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v___f_4202_; uint8_t v___x_4203_; lean_object* v___x_4204_; 
v___f_4202_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4202_, 0, v_recArgInfo_4194_);
lean_closure_set(v___f_4202_, 1, v_recArgInfos_4192_);
lean_closure_set(v___f_4202_, 2, v_positions_4193_);
lean_closure_set(v___f_4202_, 3, v_FType_4196_);
v___x_4203_ = 0;
v___x_4204_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4195_, v___f_4202_, v___x_4203_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4205_, lean_object* v_positions_4206_, lean_object* v_recArgInfo_4207_, lean_object* v_value_4208_, lean_object* v_FType_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4205_, v_positions_4206_, v_recArgInfo_4207_, v_value_4208_, v_FType_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4216_, lean_object* v_params_4217_, uint8_t v_isIndPred_4218_, lean_object* v_brecOnUniv_4219_, lean_object* v_levels_4220_, lean_object* v_idx_4221_){
_start:
{
lean_object* v_n_4222_; lean_object* v___y_4224_; 
v_n_4222_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4216_, v_idx_4221_);
if (v_isIndPred_4218_ == 0)
{
lean_object* v___x_4227_; 
v___x_4227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4227_, 0, v_brecOnUniv_4219_);
lean_ctor_set(v___x_4227_, 1, v_levels_4220_);
v___y_4224_ = v___x_4227_;
goto v___jp_4223_;
}
else
{
lean_dec(v_brecOnUniv_4219_);
v___y_4224_ = v_levels_4220_;
goto v___jp_4223_;
}
v___jp_4223_:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = l_Lean_Expr_const___override(v_n_4222_, v___y_4224_);
v___x_4226_ = l_Lean_mkAppN(v___x_4225_, v_params_4217_);
return v___x_4226_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4228_, lean_object* v_params_4229_, lean_object* v_isIndPred_4230_, lean_object* v_brecOnUniv_4231_, lean_object* v_levels_4232_, lean_object* v_idx_4233_){
_start:
{
uint8_t v_isIndPred_boxed_4234_; lean_object* v_res_4235_; 
v_isIndPred_boxed_4234_ = lean_unbox(v_isIndPred_4230_);
v_res_4235_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4228_, v_params_4229_, v_isIndPred_boxed_4234_, v_brecOnUniv_4231_, v_levels_4232_, v_idx_4233_);
lean_dec(v_idx_4233_);
lean_dec_ref(v_params_4229_);
lean_dec_ref(v_toIndGroupInfo_4228_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4236_, lean_object* v_a_4237_, lean_object* v_n_4238_){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_apply_1(v_brecOnCons_4236_, v_n_4238_);
v___x_4240_ = l_Lean_mkAppN(v___x_4239_, v_a_4237_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4241_, lean_object* v_a_4242_, lean_object* v_n_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4241_, v_a_4242_, v_n_4243_);
lean_dec_ref(v_a_4242_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4245_, lean_object* v_type_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_getLevel(v_type_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4253_, lean_object* v_type_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_res_4260_; 
v_res_4260_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4253_, v_type_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec_ref(v_x_4253_);
return v_res_4260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4261_, size_t v_sz_4262_, size_t v_i_4263_, lean_object* v_bs_4264_){
_start:
{
uint8_t v___x_4265_; 
v___x_4265_ = lean_usize_dec_lt(v_i_4263_, v_sz_4262_);
if (v___x_4265_ == 0)
{
return v_bs_4264_;
}
else
{
lean_object* v___x_4266_; lean_object* v_v_4267_; lean_object* v___x_4268_; lean_object* v_bs_x27_4269_; lean_object* v___x_4270_; size_t v___x_4271_; size_t v___x_4272_; lean_object* v___x_4273_; 
v___x_4266_ = l_Lean_instInhabitedExpr;
v_v_4267_ = lean_array_uget(v_bs_4264_, v_i_4263_);
v___x_4268_ = lean_unsigned_to_nat(0u);
v_bs_x27_4269_ = lean_array_uset(v_bs_4264_, v_i_4263_, v___x_4268_);
v___x_4270_ = lean_array_get_borrowed(v___x_4266_, v_xs_4261_, v_v_4267_);
lean_dec(v_v_4267_);
v___x_4271_ = ((size_t)1ULL);
v___x_4272_ = lean_usize_add(v_i_4263_, v___x_4271_);
lean_inc(v___x_4270_);
v___x_4273_ = lean_array_uset(v_bs_x27_4269_, v_i_4263_, v___x_4270_);
v_i_4263_ = v___x_4272_;
v_bs_4264_ = v___x_4273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4275_, lean_object* v_sz_4276_, lean_object* v_i_4277_, lean_object* v_bs_4278_){
_start:
{
size_t v_sz_boxed_4279_; size_t v_i_boxed_4280_; lean_object* v_res_4281_; 
v_sz_boxed_4279_ = lean_unbox_usize(v_sz_4276_);
lean_dec(v_sz_4276_);
v_i_boxed_4280_ = lean_unbox_usize(v_i_4277_);
lean_dec(v_i_4277_);
v_res_4281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4275_, v_sz_boxed_4279_, v_i_boxed_4280_, v_bs_4278_);
lean_dec_ref(v_xs_4275_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4282_, lean_object* v_f_4283_, lean_object* v_as_4284_, lean_object* v_bs_4285_, lean_object* v_i_4286_, lean_object* v_cs_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v___x_4293_; uint8_t v___x_4294_; 
v___x_4293_ = lean_array_get_size(v_as_4284_);
v___x_4294_ = lean_nat_dec_lt(v_i_4286_, v___x_4293_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; 
lean_dec(v_i_4286_);
lean_dec_ref(v_f_4283_);
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v_cs_4287_);
return v___x_4295_;
}
else
{
lean_object* v___x_4296_; uint8_t v___x_4297_; 
v___x_4296_ = lean_array_get_size(v_bs_4285_);
v___x_4297_ = lean_nat_dec_lt(v_i_4286_, v___x_4296_);
if (v___x_4297_ == 0)
{
lean_object* v___x_4298_; 
lean_dec(v_i_4286_);
lean_dec_ref(v_f_4283_);
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v_cs_4287_);
return v___x_4298_;
}
else
{
lean_object* v_a_4299_; lean_object* v_b_4300_; size_t v_sz_4301_; size_t v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v_a_4299_ = lean_array_fget_borrowed(v_as_4284_, v_i_4286_);
v_b_4300_ = lean_array_fget_borrowed(v_bs_4285_, v_i_4286_);
v_sz_4301_ = lean_array_size(v_b_4300_);
v___x_4302_ = ((size_t)0ULL);
lean_inc(v_b_4300_);
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4282_, v_sz_4301_, v___x_4302_, v_b_4300_);
lean_inc_ref(v_f_4283_);
lean_inc(v___y_4291_);
lean_inc_ref(v___y_4290_);
lean_inc(v___y_4289_);
lean_inc_ref(v___y_4288_);
lean_inc(v_a_4299_);
v___x_4304_ = lean_apply_7(v_f_4283_, v_a_4299_, v___x_4303_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, lean_box(0));
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4305_);
lean_dec_ref_known(v___x_4304_, 1);
v___x_4306_ = lean_unsigned_to_nat(1u);
v___x_4307_ = lean_nat_add(v_i_4286_, v___x_4306_);
lean_dec(v_i_4286_);
v___x_4308_ = lean_array_push(v_cs_4287_, v_a_4305_);
v_i_4286_ = v___x_4307_;
v_cs_4287_ = v___x_4308_;
goto _start;
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_dec_ref(v_cs_4287_);
lean_dec(v_i_4286_);
lean_dec_ref(v_f_4283_);
v_a_4310_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4304_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4304_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4318_, lean_object* v_f_4319_, lean_object* v_as_4320_, lean_object* v_bs_4321_, lean_object* v_i_4322_, lean_object* v_cs_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4318_, v_f_4319_, v_as_4320_, v_bs_4321_, v_i_4322_, v_cs_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec_ref(v_bs_4321_);
lean_dec_ref(v_as_4320_);
lean_dec_ref(v_xs_4318_);
return v_res_4329_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_Array_instInhabited___redArg();
return v___x_4330_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v_toApplicative_4338_; lean_object* v_toFunctor_4339_; lean_object* v_toSeq_4340_; lean_object* v_toSeqLeft_4341_; lean_object* v_toSeqRight_4342_; lean_object* v___f_4343_; lean_object* v___f_4344_; lean_object* v___f_4345_; lean_object* v___f_4346_; lean_object* v___x_4347_; lean_object* v___f_4348_; lean_object* v___f_4349_; lean_object* v___f_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v_toApplicative_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4385_; 
v___x_4337_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4338_ = lean_ctor_get(v___x_4337_, 0);
v_toFunctor_4339_ = lean_ctor_get(v_toApplicative_4338_, 0);
v_toSeq_4340_ = lean_ctor_get(v_toApplicative_4338_, 2);
v_toSeqLeft_4341_ = lean_ctor_get(v_toApplicative_4338_, 3);
v_toSeqRight_4342_ = lean_ctor_get(v_toApplicative_4338_, 4);
v___f_4343_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4344_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4339_, 2);
v___f_4345_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4345_, 0, v_toFunctor_4339_);
v___f_4346_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4346_, 0, v_toFunctor_4339_);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___f_4345_);
lean_ctor_set(v___x_4347_, 1, v___f_4346_);
lean_inc(v_toSeqRight_4342_);
v___f_4348_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4348_, 0, v_toSeqRight_4342_);
lean_inc(v_toSeqLeft_4341_);
v___f_4349_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4349_, 0, v_toSeqLeft_4341_);
lean_inc(v_toSeq_4340_);
v___f_4350_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4350_, 0, v_toSeq_4340_);
v___x_4351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4347_);
lean_ctor_set(v___x_4351_, 1, v___f_4343_);
lean_ctor_set(v___x_4351_, 2, v___f_4350_);
lean_ctor_set(v___x_4351_, 3, v___f_4349_);
lean_ctor_set(v___x_4351_, 4, v___f_4348_);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
lean_ctor_set(v___x_4352_, 1, v___f_4344_);
v___x_4353_ = l_StateRefT_x27_instMonad___redArg(v___x_4352_);
v_toApplicative_4354_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4385_ == 0)
{
lean_object* v_unused_4386_; 
v_unused_4386_ = lean_ctor_get(v___x_4353_, 1);
lean_dec(v_unused_4386_);
v___x_4356_ = v___x_4353_;
v_isShared_4357_ = v_isSharedCheck_4385_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_toApplicative_4354_);
lean_dec(v___x_4353_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4385_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v_toFunctor_4358_; lean_object* v_toSeq_4359_; lean_object* v_toSeqLeft_4360_; lean_object* v_toSeqRight_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4383_; 
v_toFunctor_4358_ = lean_ctor_get(v_toApplicative_4354_, 0);
v_toSeq_4359_ = lean_ctor_get(v_toApplicative_4354_, 2);
v_toSeqLeft_4360_ = lean_ctor_get(v_toApplicative_4354_, 3);
v_toSeqRight_4361_ = lean_ctor_get(v_toApplicative_4354_, 4);
v_isSharedCheck_4383_ = !lean_is_exclusive(v_toApplicative_4354_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v_toApplicative_4354_, 1);
lean_dec(v_unused_4384_);
v___x_4363_ = v_toApplicative_4354_;
v_isShared_4364_ = v_isSharedCheck_4383_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_toSeqRight_4361_);
lean_inc(v_toSeqLeft_4360_);
lean_inc(v_toSeq_4359_);
lean_inc(v_toFunctor_4358_);
lean_dec(v_toApplicative_4354_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4383_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___f_4365_; lean_object* v___f_4366_; lean_object* v___f_4367_; lean_object* v___f_4368_; lean_object* v___x_4369_; lean_object* v___f_4370_; lean_object* v___f_4371_; lean_object* v___f_4372_; lean_object* v___x_4374_; 
v___f_4365_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4358_);
v___f_4367_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4367_, 0, v_toFunctor_4358_);
v___f_4368_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4368_, 0, v_toFunctor_4358_);
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v___f_4367_);
lean_ctor_set(v___x_4369_, 1, v___f_4368_);
v___f_4370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4370_, 0, v_toSeqRight_4361_);
v___f_4371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4371_, 0, v_toSeqLeft_4360_);
v___f_4372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4372_, 0, v_toSeq_4359_);
if (v_isShared_4364_ == 0)
{
lean_ctor_set(v___x_4363_, 4, v___f_4370_);
lean_ctor_set(v___x_4363_, 3, v___f_4371_);
lean_ctor_set(v___x_4363_, 2, v___f_4372_);
lean_ctor_set(v___x_4363_, 1, v___f_4365_);
lean_ctor_set(v___x_4363_, 0, v___x_4369_);
v___x_4374_ = v___x_4363_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v___x_4369_);
lean_ctor_set(v_reuseFailAlloc_4382_, 1, v___f_4365_);
lean_ctor_set(v_reuseFailAlloc_4382_, 2, v___f_4372_);
lean_ctor_set(v_reuseFailAlloc_4382_, 3, v___f_4371_);
lean_ctor_set(v_reuseFailAlloc_4382_, 4, v___f_4370_);
v___x_4374_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4376_; 
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 1, v___f_4366_);
lean_ctor_set(v___x_4356_, 0, v___x_4374_);
v___x_4376_ = v___x_4356_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4374_);
lean_ctor_set(v_reuseFailAlloc_4381_, 1, v___f_4366_);
v___x_4376_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_855__overap_4379_; lean_object* v___x_4380_; 
v___x_4377_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4378_ = l_instInhabitedOfMonad___redArg(v___x_4376_, v___x_4377_);
v___x_855__overap_4379_ = lean_panic_fn_borrowed(v___x_4378_, v_msg_4331_);
lean_dec(v___x_4378_);
lean_inc(v___y_4335_);
lean_inc_ref(v___y_4334_);
lean_inc(v___y_4333_);
lean_inc_ref(v___y_4332_);
v___x_4380_ = lean_apply_5(v___x_855__overap_4379_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, lean_box(0));
return v___x_4380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
return v_res_4393_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4397_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4398_ = lean_unsigned_to_nat(2u);
v___x_4399_ = lean_unsigned_to_nat(73u);
v___x_4400_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4401_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4402_ = l_mkPanicMessageWithDecl(v___x_4401_, v___x_4400_, v___x_4399_, v___x_4398_, v___x_4397_);
return v___x_4402_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4404_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4405_ = lean_unsigned_to_nat(2u);
v___x_4406_ = lean_unsigned_to_nat(74u);
v___x_4407_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4408_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4409_ = l_mkPanicMessageWithDecl(v___x_4408_, v___x_4407_, v___x_4406_, v___x_4405_, v___x_4404_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4412_, lean_object* v_positions_4413_, lean_object* v_ys_4414_, lean_object* v_xs_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4421_ = lean_array_get_size(v_positions_4413_);
v___x_4422_ = lean_array_get_size(v_ys_4414_);
v___x_4423_ = lean_nat_dec_eq(v___x_4421_, v___x_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_dec_ref(v_f_4412_);
v___x_4424_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4425_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4424_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4425_;
}
else
{
lean_object* v___x_4426_; lean_object* v___x_4427_; uint8_t v___x_4428_; 
v___x_4426_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4413_);
v___x_4427_ = lean_array_get_size(v_xs_4415_);
v___x_4428_ = lean_nat_dec_eq(v___x_4426_, v___x_4427_);
lean_dec(v___x_4426_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
lean_dec_ref(v_f_4412_);
v___x_4429_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4430_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4429_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4430_;
}
else
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = lean_unsigned_to_nat(0u);
v___x_4432_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4433_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4415_, v_f_4412_, v_ys_4414_, v_positions_4413_, v___x_4431_, v___x_4432_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4434_, lean_object* v_positions_4435_, lean_object* v_ys_4436_, lean_object* v_xs_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4434_, v_positions_4435_, v_ys_4436_, v_xs_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v_xs_4437_);
lean_dec_ref(v_ys_4436_);
lean_dec_ref(v_positions_4435_);
return v_res_4443_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = lean_unsigned_to_nat(0u);
v___x_4446_ = l_Lean_Level_ofNat(v___x_4445_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4447_, lean_object* v_positions_4448_, lean_object* v_motives_4449_, uint8_t v_isIndPred_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v_indGroupInst_4459_; lean_object* v_brecOnUniv_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; 
v___x_4456_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4457_ = lean_unsigned_to_nat(0u);
v___x_4458_ = lean_array_get_borrowed(v___x_4456_, v_recArgInfos_4447_, v___x_4457_);
v_indGroupInst_4459_ = lean_ctor_get(v___x_4458_, 4);
if (v_isIndPred_4450_ == 0)
{
lean_object* v___f_4502_; lean_object* v___x_4503_; lean_object* v_motive_4504_; lean_object* v___x_4505_; 
v___f_4502_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4503_ = l_Lean_instInhabitedExpr;
v_motive_4504_ = lean_array_get_borrowed(v___x_4503_, v_motives_4449_, v___x_4457_);
lean_inc(v_motive_4504_);
v___x_4505_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4504_, v___f_4502_, v_isIndPred_4450_, v_a_4451_, v_a_4452_, v_a_4453_, v_a_4454_);
if (lean_obj_tag(v___x_4505_) == 0)
{
lean_object* v_a_4506_; 
v_a_4506_ = lean_ctor_get(v___x_4505_, 0);
lean_inc(v_a_4506_);
lean_dec_ref_known(v___x_4505_, 1);
v_brecOnUniv_4461_ = v_a_4506_;
v___y_4462_ = v_a_4451_;
v___y_4463_ = v_a_4452_;
v___y_4464_ = v_a_4453_;
v___y_4465_ = v_a_4454_;
goto v___jp_4460_;
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
v_a_4507_ = lean_ctor_get(v___x_4505_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4505_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4505_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4505_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
else
{
lean_object* v___x_4515_; 
v___x_4515_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4461_ = v___x_4515_;
v___y_4462_ = v_a_4451_;
v___y_4463_ = v_a_4452_;
v___y_4464_ = v_a_4453_;
v___y_4465_ = v_a_4454_;
goto v___jp_4460_;
}
v___jp_4460_:
{
lean_object* v_toIndGroupInfo_4466_; lean_object* v_levels_4467_; lean_object* v_params_4468_; lean_object* v___x_4469_; lean_object* v_brecOnCons_4470_; lean_object* v_brecOnAux_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v_toIndGroupInfo_4466_ = lean_ctor_get(v_indGroupInst_4459_, 0);
v_levels_4467_ = lean_ctor_get(v_indGroupInst_4459_, 1);
v_params_4468_ = lean_ctor_get(v_indGroupInst_4459_, 2);
v___x_4469_ = lean_box(v_isIndPred_4450_);
lean_inc_n(v_levels_4467_, 2);
lean_inc(v_brecOnUniv_4461_);
lean_inc_ref(v_params_4468_);
lean_inc_ref(v_toIndGroupInfo_4466_);
v_brecOnCons_4470_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4470_, 0, v_toIndGroupInfo_4466_);
lean_closure_set(v_brecOnCons_4470_, 1, v_params_4468_);
lean_closure_set(v_brecOnCons_4470_, 2, v___x_4469_);
lean_closure_set(v_brecOnCons_4470_, 3, v_brecOnUniv_4461_);
lean_closure_set(v_brecOnCons_4470_, 4, v_levels_4467_);
v_brecOnAux_4471_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4466_, v_params_4468_, v_isIndPred_4450_, v_brecOnUniv_4461_, v_levels_4467_, v___x_4457_);
v___x_4472_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4466_);
v___x_4473_ = l_Lean_Meta_inferArgumentTypesN(v___x_4472_, v_brecOnAux_4471_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4476_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4475_, v_positions_4448_, v_a_4474_, v_motives_4449_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
lean_dec(v_a_4474_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4485_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4479_ = v___x_4476_;
v_isShared_4480_ = v_isSharedCheck_4485_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4476_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4485_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___f_4481_; lean_object* v___x_4483_; 
v___f_4481_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4481_, 0, v_brecOnCons_4470_);
lean_closure_set(v___f_4481_, 1, v_a_4477_);
if (v_isShared_4480_ == 0)
{
lean_ctor_set(v___x_4479_, 0, v___f_4481_);
v___x_4483_ = v___x_4479_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___f_4481_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec_ref(v_brecOnCons_4470_);
v_a_4486_ = lean_ctor_get(v___x_4476_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4476_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4476_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4476_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec_ref(v_brecOnCons_4470_);
v_a_4494_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4473_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4473_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4516_, lean_object* v_positions_4517_, lean_object* v_motives_4518_, lean_object* v_isIndPred_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_){
_start:
{
uint8_t v_isIndPred_boxed_4525_; lean_object* v_res_4526_; 
v_isIndPred_boxed_4525_ = lean_unbox(v_isIndPred_4519_);
v_res_4526_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4516_, v_positions_4517_, v_motives_4518_, v_isIndPred_boxed_4525_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_);
lean_dec(v_a_4523_);
lean_dec_ref(v_a_4522_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec_ref(v_motives_4518_);
lean_dec_ref(v_positions_4517_);
lean_dec_ref(v_recArgInfos_4516_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4527_, lean_object* v_msg_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4535_, lean_object* v_msg_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4535_, v_msg_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4543_, lean_object* v_00_u03b1_4544_, lean_object* v_f_4545_, lean_object* v_positions_4546_, lean_object* v_ys_4547_, lean_object* v_xs_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v___x_4554_; 
v___x_4554_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4545_, v_positions_4546_, v_ys_4547_, v_xs_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4555_, lean_object* v_00_u03b1_4556_, lean_object* v_f_4557_, lean_object* v_positions_4558_, lean_object* v_ys_4559_, lean_object* v_xs_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_){
_start:
{
lean_object* v_res_4566_; 
v_res_4566_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4555_, v_00_u03b1_4556_, v_f_4557_, v_positions_4558_, v_ys_4559_, v_xs_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec_ref(v_xs_4560_);
lean_dec_ref(v_ys_4559_);
lean_dec_ref(v_positions_4558_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4567_, lean_object* v_00_u03b3_4568_, lean_object* v_xs_4569_, lean_object* v_f_4570_, lean_object* v_as_4571_, lean_object* v_bs_4572_, lean_object* v_i_4573_, lean_object* v_cs_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v___x_4580_; 
v___x_4580_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4569_, v_f_4570_, v_as_4571_, v_bs_4572_, v_i_4573_, v_cs_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4581_, lean_object* v_00_u03b3_4582_, lean_object* v_xs_4583_, lean_object* v_f_4584_, lean_object* v_as_4585_, lean_object* v_bs_4586_, lean_object* v_i_4587_, lean_object* v_cs_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v_res_4594_; 
v_res_4594_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4581_, v_00_u03b3_4582_, v_xs_4583_, v_f_4584_, v_as_4585_, v_bs_4586_, v_i_4587_, v_cs_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec_ref(v_bs_4586_);
lean_dec_ref(v_as_4585_);
lean_dec_ref(v_xs_4583_);
return v_res_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(lean_object* v_type_4595_, lean_object* v_maxFVars_x3f_4596_, lean_object* v_k_4597_, uint8_t v_cleanupAnnotations_4598_, uint8_t v_whnfType_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v___f_4605_; lean_object* v___x_4606_; 
v___f_4605_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4605_, 0, v_k_4597_);
v___x_4606_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4595_, v_maxFVars_x3f_4596_, v___f_4605_, v_cleanupAnnotations_4598_, v_whnfType_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4614_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4609_ = v___x_4606_;
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4614_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4612_; 
if (v_isShared_4610_ == 0)
{
v___x_4612_ = v___x_4609_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_a_4607_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
v_a_4615_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4606_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4606_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg___boxed(lean_object* v_type_4623_, lean_object* v_maxFVars_x3f_4624_, lean_object* v_k_4625_, lean_object* v_cleanupAnnotations_4626_, lean_object* v_whnfType_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4633_; uint8_t v_whnfType_boxed_4634_; lean_object* v_res_4635_; 
v_cleanupAnnotations_boxed_4633_ = lean_unbox(v_cleanupAnnotations_4626_);
v_whnfType_boxed_4634_ = lean_unbox(v_whnfType_4627_);
v_res_4635_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4623_, v_maxFVars_x3f_4624_, v_k_4625_, v_cleanupAnnotations_boxed_4633_, v_whnfType_boxed_4634_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_00_u03b1_4636_, lean_object* v_type_4637_, lean_object* v_maxFVars_x3f_4638_, lean_object* v_k_4639_, uint8_t v_cleanupAnnotations_4640_, uint8_t v_whnfType_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4637_, v_maxFVars_x3f_4638_, v_k_4639_, v_cleanupAnnotations_4640_, v_whnfType_4641_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_00_u03b1_4648_, lean_object* v_type_4649_, lean_object* v_maxFVars_x3f_4650_, lean_object* v_k_4651_, lean_object* v_cleanupAnnotations_4652_, lean_object* v_whnfType_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4659_; uint8_t v_whnfType_boxed_4660_; lean_object* v_res_4661_; 
v_cleanupAnnotations_boxed_4659_ = lean_unbox(v_cleanupAnnotations_4652_);
v_whnfType_boxed_4660_ = lean_unbox(v_whnfType_4653_);
v_res_4661_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_00_u03b1_4648_, v_type_4649_, v_maxFVars_x3f_4650_, v_k_4651_, v_cleanupAnnotations_boxed_4659_, v_whnfType_boxed_4660_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v_numTypeFormers_4662_, lean_object* v_x_4663_, lean_object* v_brecOnType_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4662_, v_brecOnType_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed(lean_object* v_numTypeFormers_4671_, lean_object* v_x_4672_, lean_object* v_brecOnType_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(v_numTypeFormers_4671_, v_x_4672_, v_brecOnType_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec_ref(v_x_4672_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v___x_4680_, lean_object* v_e_4681_){
_start:
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = l_Lean_indentD(v_e_4681_);
v___x_4683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4683_, 0, v___x_4680_);
lean_ctor_set(v___x_4683_, 1, v___x_4682_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4684_, lean_object* v_as_4685_, size_t v_sz_4686_, size_t v_i_4687_, lean_object* v_b_4688_){
_start:
{
uint8_t v___x_4690_; 
v___x_4690_ = lean_usize_dec_lt(v_i_4687_, v_sz_4686_);
if (v___x_4690_ == 0)
{
lean_object* v___x_4691_; 
lean_dec_ref(v_a_4684_);
v___x_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4691_, 0, v_b_4688_);
return v___x_4691_;
}
else
{
lean_object* v_a_4692_; lean_object* v___x_4693_; size_t v___x_4694_; size_t v___x_4695_; 
v_a_4692_ = lean_array_uget_borrowed(v_as_4685_, v_i_4687_);
lean_inc_ref(v_a_4684_);
v___x_4693_ = lean_array_set(v_b_4688_, v_a_4692_, v_a_4684_);
v___x_4694_ = ((size_t)1ULL);
v___x_4695_ = lean_usize_add(v_i_4687_, v___x_4694_);
v_i_4687_ = v___x_4695_;
v_b_4688_ = v___x_4693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4697_, lean_object* v_as_4698_, lean_object* v_sz_4699_, lean_object* v_i_4700_, lean_object* v_b_4701_, lean_object* v___y_4702_){
_start:
{
size_t v_sz_boxed_4703_; size_t v_i_boxed_4704_; lean_object* v_res_4705_; 
v_sz_boxed_4703_ = lean_unbox_usize(v_sz_4699_);
lean_dec(v_sz_4699_);
v_i_boxed_4704_ = lean_unbox_usize(v_i_4700_);
lean_dec(v_i_4700_);
v_res_4705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4697_, v_as_4698_, v_sz_boxed_4703_, v_i_boxed_4704_, v_b_4701_);
lean_dec_ref(v_as_4698_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(lean_object* v_as_4706_, size_t v_sz_4707_, size_t v_i_4708_, lean_object* v_b_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
uint8_t v___x_4715_; 
v___x_4715_ = lean_usize_dec_lt(v_i_4708_, v_sz_4707_);
if (v___x_4715_ == 0)
{
lean_object* v___x_4716_; 
v___x_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4716_, 0, v_b_4709_);
return v___x_4716_;
}
else
{
lean_object* v_snd_4717_; lean_object* v_fst_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4762_; 
v_snd_4717_ = lean_ctor_get(v_b_4709_, 1);
v_fst_4718_ = lean_ctor_get(v_b_4709_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v_b_4709_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4720_ = v_b_4709_;
v_isShared_4721_ = v_isSharedCheck_4762_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_snd_4717_);
lean_inc(v_fst_4718_);
lean_dec(v_b_4709_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4762_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v_array_4722_; lean_object* v_start_4723_; lean_object* v_stop_4724_; uint8_t v___x_4725_; 
v_array_4722_ = lean_ctor_get(v_snd_4717_, 0);
v_start_4723_ = lean_ctor_get(v_snd_4717_, 1);
v_stop_4724_ = lean_ctor_get(v_snd_4717_, 2);
v___x_4725_ = lean_nat_dec_lt(v_start_4723_, v_stop_4724_);
if (v___x_4725_ == 0)
{
lean_object* v___x_4727_; 
if (v_isShared_4721_ == 0)
{
v___x_4727_ = v___x_4720_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_fst_4718_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v_snd_4717_);
v___x_4727_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
lean_object* v___x_4728_; 
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4727_);
return v___x_4728_;
}
}
else
{
lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4758_; 
lean_inc(v_stop_4724_);
lean_inc(v_start_4723_);
lean_inc_ref(v_array_4722_);
v_isSharedCheck_4758_ = !lean_is_exclusive(v_snd_4717_);
if (v_isSharedCheck_4758_ == 0)
{
lean_object* v_unused_4759_; lean_object* v_unused_4760_; lean_object* v_unused_4761_; 
v_unused_4759_ = lean_ctor_get(v_snd_4717_, 2);
lean_dec(v_unused_4759_);
v_unused_4760_ = lean_ctor_get(v_snd_4717_, 1);
lean_dec(v_unused_4760_);
v_unused_4761_ = lean_ctor_get(v_snd_4717_, 0);
lean_dec(v_unused_4761_);
v___x_4731_ = v_snd_4717_;
v_isShared_4732_ = v_isSharedCheck_4758_;
goto v_resetjp_4730_;
}
else
{
lean_dec(v_snd_4717_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4758_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v_a_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4738_; 
v_a_4733_ = lean_array_uget_borrowed(v_as_4706_, v_i_4708_);
v___x_4734_ = lean_array_fget(v_array_4722_, v_start_4723_);
v___x_4735_ = lean_unsigned_to_nat(1u);
v___x_4736_ = lean_nat_add(v_start_4723_, v___x_4735_);
lean_dec(v_start_4723_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set(v___x_4731_, 1, v___x_4736_);
v___x_4738_ = v___x_4731_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_array_4722_);
lean_ctor_set(v_reuseFailAlloc_4757_, 1, v___x_4736_);
lean_ctor_set(v_reuseFailAlloc_4757_, 2, v_stop_4724_);
v___x_4738_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
size_t v_sz_4739_; size_t v___x_4740_; lean_object* v___x_4741_; 
v_sz_4739_ = lean_array_size(v___x_4734_);
v___x_4740_ = ((size_t)0ULL);
lean_inc(v_a_4733_);
v___x_4741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4733_, v___x_4734_, v_sz_4739_, v___x_4740_, v_fst_4718_);
lean_dec(v___x_4734_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v___x_4744_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4742_);
lean_dec_ref_known(v___x_4741_, 1);
if (v_isShared_4721_ == 0)
{
lean_ctor_set(v___x_4720_, 1, v___x_4738_);
lean_ctor_set(v___x_4720_, 0, v_a_4742_);
v___x_4744_ = v___x_4720_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
lean_ctor_set(v_reuseFailAlloc_4748_, 1, v___x_4738_);
v___x_4744_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
size_t v___x_4745_; size_t v___x_4746_; 
v___x_4745_ = ((size_t)1ULL);
v___x_4746_ = lean_usize_add(v_i_4708_, v___x_4745_);
v_i_4708_ = v___x_4746_;
v_b_4709_ = v___x_4744_;
goto _start;
}
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
lean_dec_ref(v___x_4738_);
lean_del_object(v___x_4720_);
v_a_4749_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4741_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4741_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2___boxed(lean_object* v_as_4763_, lean_object* v_sz_4764_, lean_object* v_i_4765_, lean_object* v_b_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_){
_start:
{
size_t v_sz_boxed_4772_; size_t v_i_boxed_4773_; lean_object* v_res_4774_; 
v_sz_boxed_4772_ = lean_unbox_usize(v_sz_4764_);
lean_dec(v_sz_4764_);
v_i_boxed_4773_ = lean_unbox_usize(v_i_4765_);
lean_dec(v_i_4765_);
v_res_4774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_as_4763_, v_sz_boxed_4772_, v_i_boxed_4773_, v_b_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec_ref(v_as_4763_);
return v_res_4774_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4777_ = l_Lean_stringToMessageData(v___x_4776_);
return v___x_4777_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___f_4779_; 
v___x_4778_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4779_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1), 2, 1);
lean_closure_set(v___f_4779_, 0, v___x_4778_);
return v___f_4779_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4780_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4781_ = l_Lean_Expr_sort___override(v___x_4780_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4782_, lean_object* v_positions_4783_, lean_object* v_brecOnConst_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v_recArgInfo_4792_; lean_object* v_indicesPos_4793_; lean_object* v_indIdx_4794_; lean_object* v_numTypeFormers_4795_; lean_object* v___f_4796_; lean_object* v_brecOn_4797_; lean_object* v___f_4798_; uint8_t v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4790_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4791_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4792_ = lean_array_get_borrowed(v___x_4790_, v_recArgInfos_4782_, v___x_4791_);
v_indicesPos_4793_ = lean_ctor_get(v_recArgInfo_4792_, 3);
v_indIdx_4794_ = lean_ctor_get(v_recArgInfo_4792_, 5);
v_numTypeFormers_4795_ = lean_array_get_size(v_positions_4783_);
v___f_4796_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4796_, 0, v_numTypeFormers_4795_);
lean_inc(v_indIdx_4794_);
v_brecOn_4797_ = lean_apply_1(v_brecOnConst_4784_, v_indIdx_4794_);
v___f_4798_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4799_ = 0;
v___x_4800_ = lean_box(v___x_4799_);
lean_inc_ref(v_brecOn_4797_);
v___x_4801_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4801_, 0, v_brecOn_4797_);
lean_closure_set(v___x_4801_, 1, v___x_4800_);
v___x_4802_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4801_, v___f_4798_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v___x_4803_; 
lean_dec_ref_known(v___x_4802_, 1);
lean_inc(v_a_4788_);
lean_inc_ref(v_a_4787_);
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
v___x_4803_ = lean_infer_type(v_brecOn_4797_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
if (lean_obj_tag(v___x_4803_) == 0)
{
lean_object* v_a_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; uint8_t v___x_4809_; lean_object* v___x_4810_; 
v_a_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc(v_a_4804_);
lean_dec_ref_known(v___x_4803_, 1);
v___x_4805_ = lean_array_get_size(v_indicesPos_4793_);
v___x_4806_ = lean_unsigned_to_nat(1u);
v___x_4807_ = lean_nat_add(v___x_4805_, v___x_4806_);
v___x_4808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4807_);
v___x_4809_ = 0;
v___x_4810_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_a_4804_, v___x_4808_, v___f_4796_, v___x_4809_, v___x_4809_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; size_t v_sz_4817_; size_t v___x_4818_; lean_object* v___x_4819_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_a_4811_);
lean_dec_ref_known(v___x_4810_, 1);
v___x_4812_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4783_);
v___x_4813_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4814_ = lean_mk_array(v___x_4812_, v___x_4813_);
v___x_4815_ = l_Array_toSubarray___redArg(v_positions_4783_, v___x_4791_, v_numTypeFormers_4795_);
v___x_4816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4814_);
lean_ctor_set(v___x_4816_, 1, v___x_4815_);
v_sz_4817_ = lean_array_size(v_a_4811_);
v___x_4818_ = ((size_t)0ULL);
v___x_4819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_a_4811_, v_sz_4817_, v___x_4818_, v___x_4816_, v_a_4785_, v_a_4786_, v_a_4787_, v_a_4788_);
lean_dec(v_a_4811_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4828_; 
v_a_4820_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4822_ = v___x_4819_;
v_isShared_4823_ = v_isSharedCheck_4828_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4819_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4828_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v_fst_4824_; lean_object* v___x_4826_; 
v_fst_4824_ = lean_ctor_get(v_a_4820_, 0);
lean_inc(v_fst_4824_);
lean_dec(v_a_4820_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v_fst_4824_);
v___x_4826_ = v___x_4822_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_fst_4824_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
v_a_4829_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4819_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4819_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4783_);
return v___x_4810_;
}
}
else
{
lean_object* v_a_4837_; lean_object* v___x_4839_; uint8_t v_isShared_4840_; uint8_t v_isSharedCheck_4844_; 
lean_dec_ref(v___f_4796_);
lean_dec_ref(v_positions_4783_);
v_a_4837_ = lean_ctor_get(v___x_4803_, 0);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4803_);
if (v_isSharedCheck_4844_ == 0)
{
v___x_4839_ = v___x_4803_;
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
else
{
lean_inc(v_a_4837_);
lean_dec(v___x_4803_);
v___x_4839_ = lean_box(0);
v_isShared_4840_ = v_isSharedCheck_4844_;
goto v_resetjp_4838_;
}
v_resetjp_4838_:
{
lean_object* v___x_4842_; 
if (v_isShared_4840_ == 0)
{
v___x_4842_ = v___x_4839_;
goto v_reusejp_4841_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
v___x_4842_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4841_;
}
v_reusejp_4841_:
{
return v___x_4842_;
}
}
}
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4852_; 
lean_dec_ref(v_brecOn_4797_);
lean_dec_ref(v___f_4796_);
lean_dec_ref(v_positions_4783_);
v_a_4845_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4847_ = v___x_4802_;
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4802_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4850_; 
if (v_isShared_4848_ == 0)
{
v___x_4850_ = v___x_4847_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4853_, lean_object* v_positions_4854_, lean_object* v_brecOnConst_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4853_, v_positions_4854_, v_brecOnConst_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec_ref(v_recArgInfos_4853_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4862_, lean_object* v_as_4863_, size_t v_sz_4864_, size_t v_i_4865_, lean_object* v_b_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4862_, v_as_4863_, v_sz_4864_, v_i_4865_, v_b_4866_);
return v___x_4872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4873_, lean_object* v_as_4874_, lean_object* v_sz_4875_, lean_object* v_i_4876_, lean_object* v_b_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
size_t v_sz_boxed_4883_; size_t v_i_boxed_4884_; lean_object* v_res_4885_; 
v_sz_boxed_4883_ = lean_unbox_usize(v_sz_4875_);
lean_dec(v_sz_4875_);
v_i_boxed_4884_ = lean_unbox_usize(v_i_4876_);
lean_dec(v_i_4876_);
v_res_4885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4873_, v_as_4874_, v_sz_boxed_4883_, v_i_boxed_4884_, v_b_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_);
lean_dec(v___y_4881_);
lean_dec_ref(v___y_4880_);
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
lean_dec_ref(v_as_4874_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4886_, lean_object* v_a_4887_){
_start:
{
if (lean_obj_tag(v_a_4886_) == 0)
{
lean_object* v___x_4888_; 
v___x_4888_ = l_List_reverse___redArg(v_a_4887_);
return v___x_4888_;
}
else
{
lean_object* v_head_4889_; lean_object* v_tail_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4901_; 
v_head_4889_ = lean_ctor_get(v_a_4886_, 0);
v_tail_4890_ = lean_ctor_get(v_a_4886_, 1);
v_isSharedCheck_4901_ = !lean_is_exclusive(v_a_4886_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4892_ = v_a_4886_;
v_isShared_4893_ = v_isSharedCheck_4901_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_tail_4890_);
lean_inc(v_head_4889_);
lean_dec(v_a_4886_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4901_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4898_; 
v___x_4894_ = l_Nat_reprFast(v_head_4889_);
v___x_4895_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4894_);
v___x_4896_ = l_Lean_MessageData_ofFormat(v___x_4895_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 1, v_a_4887_);
lean_ctor_set(v___x_4892_, 0, v___x_4896_);
v___x_4898_ = v___x_4892_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4896_);
lean_ctor_set(v_reuseFailAlloc_4900_, 1, v_a_4887_);
v___x_4898_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
v_a_4886_ = v_tail_4890_;
v_a_4887_ = v___x_4898_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4902_, lean_object* v_a_4903_){
_start:
{
if (lean_obj_tag(v_a_4902_) == 0)
{
lean_object* v___x_4904_; 
v___x_4904_ = l_List_reverse___redArg(v_a_4903_);
return v___x_4904_;
}
else
{
lean_object* v_head_4905_; lean_object* v_tail_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4918_; 
v_head_4905_ = lean_ctor_get(v_a_4902_, 0);
v_tail_4906_ = lean_ctor_get(v_a_4902_, 1);
v_isSharedCheck_4918_ = !lean_is_exclusive(v_a_4902_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4908_ = v_a_4902_;
v_isShared_4909_ = v_isSharedCheck_4918_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_tail_4906_);
lean_inc(v_head_4905_);
lean_dec(v_a_4902_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4918_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4915_; 
v___x_4910_ = lean_array_to_list(v_head_4905_);
v___x_4911_ = lean_box(0);
v___x_4912_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4910_, v___x_4911_);
v___x_4913_ = l_Lean_MessageData_ofList(v___x_4912_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 1, v_a_4903_);
lean_ctor_set(v___x_4908_, 0, v___x_4913_);
v___x_4915_ = v___x_4908_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4913_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v_a_4903_);
v___x_4915_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
v_a_4902_ = v_tail_4906_;
v_a_4903_ = v___x_4915_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4919_, lean_object* v_v_4920_, lean_object* v_i_4921_){
_start:
{
lean_object* v___x_4922_; uint8_t v___x_4923_; 
v___x_4922_ = lean_array_get_size(v_xs_4919_);
v___x_4923_ = lean_nat_dec_lt(v_i_4921_, v___x_4922_);
if (v___x_4923_ == 0)
{
lean_object* v___x_4924_; 
lean_dec(v_i_4921_);
v___x_4924_ = lean_box(0);
return v___x_4924_;
}
else
{
lean_object* v___x_4925_; uint8_t v___x_4926_; 
v___x_4925_ = lean_array_fget_borrowed(v_xs_4919_, v_i_4921_);
v___x_4926_ = lean_nat_dec_eq(v___x_4925_, v_v_4920_);
if (v___x_4926_ == 0)
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_unsigned_to_nat(1u);
v___x_4928_ = lean_nat_add(v_i_4921_, v___x_4927_);
lean_dec(v_i_4921_);
v_i_4921_ = v___x_4928_;
goto _start;
}
else
{
lean_object* v___x_4930_; 
v___x_4930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4930_, 0, v_i_4921_);
return v___x_4930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4931_, lean_object* v_v_4932_, lean_object* v_i_4933_){
_start:
{
lean_object* v_res_4934_; 
v_res_4934_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4931_, v_v_4932_, v_i_4933_);
lean_dec(v_v_4932_);
lean_dec_ref(v_xs_4931_);
return v_res_4934_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4935_, lean_object* v_v_4936_){
_start:
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = lean_unsigned_to_nat(0u);
v___x_4938_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4935_, v_v_4936_, v___x_4937_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4939_, lean_object* v_v_4940_){
_start:
{
lean_object* v_res_4941_; 
v_res_4941_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4939_, v_v_4940_);
lean_dec(v_v_4940_);
lean_dec_ref(v_xs_4939_);
return v_res_4941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4945_, lean_object* v_as_4946_, size_t v_sz_4947_, size_t v_i_4948_, lean_object* v_b_4949_){
_start:
{
uint8_t v___x_4950_; 
v___x_4950_ = lean_usize_dec_lt(v_i_4948_, v_sz_4947_);
if (v___x_4950_ == 0)
{
lean_inc_ref(v_b_4949_);
return v_b_4949_;
}
else
{
lean_object* v___x_4951_; lean_object* v_a_4952_; lean_object* v___x_4953_; 
v___x_4951_ = lean_box(0);
v_a_4952_ = lean_array_uget_borrowed(v_as_4946_, v_i_4948_);
v___x_4953_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4952_, v_fnIdx_4945_);
if (lean_obj_tag(v___x_4953_) == 0)
{
lean_object* v___x_4954_; size_t v___x_4955_; size_t v___x_4956_; 
v___x_4954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4955_ = ((size_t)1ULL);
v___x_4956_ = lean_usize_add(v_i_4948_, v___x_4955_);
v_i_4948_ = v___x_4956_;
v_b_4949_ = v___x_4954_;
goto _start;
}
else
{
lean_object* v_val_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4969_; 
v_val_4958_ = lean_ctor_get(v___x_4953_, 0);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4953_);
if (v_isSharedCheck_4969_ == 0)
{
v___x_4960_ = v___x_4953_;
v_isShared_4961_ = v_isSharedCheck_4969_;
goto v_resetjp_4959_;
}
else
{
lean_inc(v_val_4958_);
lean_dec(v___x_4953_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4969_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4965_; 
v___x_4962_ = lean_array_get_size(v_a_4952_);
v___x_4963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4963_, 0, v___x_4962_);
lean_ctor_set(v___x_4963_, 1, v_val_4958_);
if (v_isShared_4961_ == 0)
{
lean_ctor_set(v___x_4960_, 0, v___x_4963_);
v___x_4965_ = v___x_4960_;
goto v_reusejp_4964_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v___x_4963_);
v___x_4965_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4964_;
}
v_reusejp_4964_:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4965_);
v___x_4967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4966_);
lean_ctor_set(v___x_4967_, 1, v___x_4951_);
return v___x_4967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4970_, lean_object* v_as_4971_, lean_object* v_sz_4972_, lean_object* v_i_4973_, lean_object* v_b_4974_){
_start:
{
size_t v_sz_boxed_4975_; size_t v_i_boxed_4976_; lean_object* v_res_4977_; 
v_sz_boxed_4975_ = lean_unbox_usize(v_sz_4972_);
lean_dec(v_sz_4972_);
v_i_boxed_4976_ = lean_unbox_usize(v_i_4973_);
lean_dec(v_i_4973_);
v_res_4977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4970_, v_as_4971_, v_sz_boxed_4975_, v_i_boxed_4976_, v_b_4974_);
lean_dec_ref(v_b_4974_);
lean_dec_ref(v_as_4971_);
lean_dec(v_fnIdx_4970_);
return v_res_4977_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4979_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4980_ = l_Lean_stringToMessageData(v___x_4979_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4981_, lean_object* v_positions_4982_, lean_object* v_fnIdx_4983_, lean_object* v_brecOnConst_4984_, lean_object* v_packedFArgs_4985_, lean_object* v_funTypes_4986_, lean_object* v_ys_4987_, lean_object* v___value_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_5008_; lean_object* v_fst_5009_; lean_object* v_snd_5010_; lean_object* v___x_5011_; size_t v_sz_5012_; size_t v___x_5013_; lean_object* v___x_5014_; lean_object* v_fst_5015_; 
lean_inc_ref(v_ys_4987_);
lean_inc_ref(v_recArgInfo_4981_);
v___x_5008_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4981_, v_ys_4987_);
v_fst_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc(v_fst_5009_);
v_snd_5010_ = lean_ctor_get(v___x_5008_, 1);
lean_inc(v_snd_5010_);
lean_dec_ref(v___x_5008_);
v___x_5011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5012_ = lean_array_size(v_positions_4982_);
v___x_5013_ = ((size_t)0ULL);
v___x_5014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4983_, v_positions_4982_, v_sz_5012_, v___x_5013_, v___x_5011_);
v_fst_5015_ = lean_ctor_get(v___x_5014_, 0);
lean_inc(v_fst_5015_);
lean_dec_ref(v___x_5014_);
if (lean_obj_tag(v_fst_5015_) == 0)
{
lean_dec(v_snd_5010_);
lean_dec(v_fst_5009_);
lean_dec_ref(v_ys_4987_);
lean_dec_ref(v_brecOnConst_4984_);
lean_dec_ref(v_recArgInfo_4981_);
goto v___jp_4994_;
}
else
{
lean_object* v_val_5016_; 
v_val_5016_ = lean_ctor_get(v_fst_5015_, 0);
lean_inc(v_val_5016_);
lean_dec_ref_known(v_fst_5015_, 1);
if (lean_obj_tag(v_val_5016_) == 1)
{
lean_object* v_val_5017_; lean_object* v_fst_5018_; lean_object* v_snd_5019_; lean_object* v_indIdx_5020_; lean_object* v_brecOn_5021_; lean_object* v_brecOn_5022_; lean_object* v_brecOn_5023_; lean_object* v___x_5024_; 
lean_dec(v_fnIdx_4983_);
lean_dec_ref(v_positions_4982_);
v_val_5017_ = lean_ctor_get(v_val_5016_, 0);
lean_inc(v_val_5017_);
lean_dec_ref_known(v_val_5016_, 1);
v_fst_5018_ = lean_ctor_get(v_val_5017_, 0);
lean_inc(v_fst_5018_);
v_snd_5019_ = lean_ctor_get(v_val_5017_, 1);
lean_inc(v_snd_5019_);
lean_dec(v_val_5017_);
v_indIdx_5020_ = lean_ctor_get(v_recArgInfo_4981_, 5);
lean_inc(v_indIdx_5020_);
lean_dec_ref(v_recArgInfo_4981_);
v_brecOn_5021_ = lean_apply_1(v_brecOnConst_4984_, v_indIdx_5020_);
v_brecOn_5022_ = l_Lean_mkAppN(v_brecOn_5021_, v_fst_5009_);
lean_dec(v_fst_5009_);
v_brecOn_5023_ = l_Lean_mkAppN(v_brecOn_5022_, v_packedFArgs_4985_);
v___x_5024_ = l_Lean_Meta_PProdN_projM(v_fst_5018_, v_snd_5019_, v_brecOn_5023_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
lean_dec(v_snd_5019_);
lean_dec(v_fst_5018_);
if (lean_obj_tag(v___x_5024_) == 0)
{
lean_object* v_a_5025_; lean_object* v___x_5026_; uint8_t v___x_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; 
v_a_5025_ = lean_ctor_get(v___x_5024_, 0);
lean_inc(v_a_5025_);
lean_dec_ref_known(v___x_5024_, 1);
v___x_5026_ = l_Lean_mkAppN(v_a_5025_, v_snd_5010_);
lean_dec(v_snd_5010_);
v___x_5027_ = 1;
v___x_5028_ = 1;
v___x_5029_ = l_Lean_Meta_mkLetFVars(v_funTypes_4986_, v___x_5026_, v___x_5027_, v___x_5027_, v___x_5028_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; uint8_t v___x_5031_; lean_object* v___x_5032_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref_known(v___x_5029_, 1);
v___x_5031_ = 0;
v___x_5032_ = l_Lean_Meta_mkLambdaFVars(v_ys_4987_, v_a_5030_, v___x_5031_, v___x_5027_, v___x_5031_, v___x_5027_, v___x_5028_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
lean_dec_ref(v_ys_4987_);
return v___x_5032_;
}
else
{
lean_dec_ref(v_ys_4987_);
return v___x_5029_;
}
}
else
{
lean_dec(v_snd_5010_);
lean_dec_ref(v_ys_4987_);
return v___x_5024_;
}
}
else
{
lean_dec(v_val_5016_);
lean_dec(v_snd_5010_);
lean_dec(v_fst_5009_);
lean_dec_ref(v_ys_4987_);
lean_dec_ref(v_brecOnConst_4984_);
lean_dec_ref(v_recArgInfo_4981_);
goto v___jp_4994_;
}
}
v___jp_4994_:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_4995_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_4996_ = l_Nat_reprFast(v_fnIdx_4983_);
v___x_4997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4996_);
v___x_4998_ = l_Lean_MessageData_ofFormat(v___x_4997_);
v___x_4999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4995_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
v___x_5000_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___x_4999_);
lean_ctor_set(v___x_5001_, 1, v___x_5000_);
v___x_5002_ = lean_array_to_list(v_positions_4982_);
v___x_5003_ = lean_box(0);
v___x_5004_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5002_, v___x_5003_);
v___x_5005_ = l_Lean_MessageData_ofList(v___x_5004_);
v___x_5006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5001_);
lean_ctor_set(v___x_5006_, 1, v___x_5005_);
v___x_5007_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5006_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
return v___x_5007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5033_, lean_object* v_positions_5034_, lean_object* v_fnIdx_5035_, lean_object* v_brecOnConst_5036_, lean_object* v_packedFArgs_5037_, lean_object* v_funTypes_5038_, lean_object* v_ys_5039_, lean_object* v___value_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v_res_5046_; 
v_res_5046_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5033_, v_positions_5034_, v_fnIdx_5035_, v_brecOnConst_5036_, v_packedFArgs_5037_, v_funTypes_5038_, v_ys_5039_, v___value_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec_ref(v___value_5040_);
lean_dec_ref(v_funTypes_5038_);
lean_dec_ref(v_packedFArgs_5037_);
return v_res_5046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5047_, lean_object* v_fnIdx_5048_, lean_object* v_brecOnConst_5049_, lean_object* v_packedFArgs_5050_, lean_object* v_funTypes_5051_, lean_object* v_recArgInfo_5052_, lean_object* v_value_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_, lean_object* v_a_5057_){
_start:
{
lean_object* v___f_5059_; uint8_t v___x_5060_; lean_object* v___x_5061_; 
v___f_5059_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5059_, 0, v_recArgInfo_5052_);
lean_closure_set(v___f_5059_, 1, v_positions_5047_);
lean_closure_set(v___f_5059_, 2, v_fnIdx_5048_);
lean_closure_set(v___f_5059_, 3, v_brecOnConst_5049_);
lean_closure_set(v___f_5059_, 4, v_packedFArgs_5050_);
lean_closure_set(v___f_5059_, 5, v_funTypes_5051_);
v___x_5060_ = 0;
v___x_5061_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5053_, v___f_5059_, v___x_5060_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5062_, lean_object* v_fnIdx_5063_, lean_object* v_brecOnConst_5064_, lean_object* v_packedFArgs_5065_, lean_object* v_funTypes_5066_, lean_object* v_recArgInfo_5067_, lean_object* v_value_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_){
_start:
{
lean_object* v_res_5074_; 
v_res_5074_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5062_, v_fnIdx_5063_, v_brecOnConst_5064_, v_packedFArgs_5065_, v_funTypes_5066_, v_recArgInfo_5067_, v_value_5068_, v_a_5069_, v_a_5070_, v_a_5071_, v_a_5072_);
lean_dec(v_a_5072_);
lean_dec_ref(v_a_5071_);
lean_dec(v_a_5070_);
lean_dec_ref(v_a_5069_);
return v_res_5074_;
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
