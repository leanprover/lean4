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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* v_a_132_; uint8_t v___y_134_; uint8_t v___x_147_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v___x_147_ = l_Lean_Exception_isInterrupt(v_a_132_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
lean_inc(v_a_132_);
v___x_148_ = l_Lean_Exception_isRuntime(v_a_132_);
v___y_134_ = v___x_148_;
goto v___jp_133_;
}
else
{
v___y_134_ = v___x_147_;
goto v___jp_133_;
}
v___jp_133_:
{
if (v___y_134_ == 0)
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
}
}
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v___x_128_);
lean_dec_ref(v_arg_119_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
v_a_149_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_129_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_129_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec_ref(v_str_120_);
lean_dec_ref(v_e_104_);
v___x_157_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__3));
v___x_158_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_105_);
v___x_159_ = l_Lean_Expr_proj___override(v___x_157_, v___x_158_, v_F_105_);
v___x_160_ = l_Lean_Meta_saveState___redArg(v_a_108_, v_a_110_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
lean_inc_ref(v_k_106_);
v___x_162_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_119_, v___x_159_, v_k_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_dec(v_a_161_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_162_;
}
else
{
lean_object* v_a_163_; uint8_t v___y_165_; uint8_t v___x_178_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
v___x_178_ = l_Lean_Exception_isInterrupt(v_a_163_);
if (v___x_178_ == 0)
{
uint8_t v___x_179_; 
lean_inc(v_a_163_);
v___x_179_ = l_Lean_Exception_isRuntime(v_a_163_);
v___y_165_ = v___x_179_;
goto v___jp_164_;
}
else
{
v___y_165_ = v___x_178_;
goto v___jp_164_;
}
v___jp_164_:
{
if (v___y_165_ == 0)
{
lean_object* v___x_166_; 
lean_dec_ref_known(v___x_162_, 1);
v___x_166_ = l_Lean_Meta_SavedState_restore___redArg(v_a_161_, v_a_108_, v_a_110_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref_known(v___x_166_, 1);
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = l_Lean_Expr_proj___override(v___x_157_, v___x_167_, v_F_105_);
v_e_104_ = v_arg_118_;
v_F_105_ = v___x_168_;
goto _start;
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
v_a_170_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_166_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_166_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_dec(v_a_161_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec_ref(v___x_159_);
lean_dec_ref(v_arg_119_);
lean_dec_ref(v_arg_118_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
v_a_180_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_160_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_160_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
else
{
lean_object* v___x_188_; 
lean_dec_ref_known(v_declName_116_, 2);
lean_dec_ref_known(v_fn_114_, 2);
lean_dec_ref_known(v_a_113_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_188_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_188_;
}
}
else
{
lean_object* v___x_189_; 
lean_dec(v_declName_116_);
lean_dec_ref_known(v_fn_114_, 2);
lean_dec_ref_known(v_a_113_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_189_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_189_;
}
}
else
{
lean_object* v___x_190_; 
lean_dec_ref_known(v_fn_114_, 2);
lean_dec_ref_known(v_a_113_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_190_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_190_;
}
}
else
{
lean_object* v___x_191_; 
lean_dec_ref_known(v_a_113_, 2);
lean_dec_ref(v_fn_114_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_191_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_191_;
}
}
case 4:
{
lean_object* v_declName_192_; 
v_declName_192_ = lean_ctor_get(v_a_113_, 0);
lean_inc(v_declName_192_);
lean_dec_ref_known(v_a_113_, 2);
if (lean_obj_tag(v_declName_192_) == 1)
{
lean_object* v_pre_193_; 
v_pre_193_ = lean_ctor_get(v_declName_192_, 0);
if (lean_obj_tag(v_pre_193_) == 0)
{
lean_object* v_str_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_str_194_ = lean_ctor_get(v_declName_192_, 1);
lean_inc_ref(v_str_194_);
lean_dec_ref_known(v_declName_192_, 2);
v___x_195_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__4));
v___x_196_ = lean_string_dec_eq(v_str_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__5));
v___x_198_ = lean_string_dec_eq(v_str_194_, v___x_197_);
lean_dec_ref(v_str_194_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; 
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_199_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_199_;
}
else
{
lean_object* v___x_200_; 
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
lean_dec_ref(v_e_104_);
v___x_200_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_200_;
}
}
else
{
lean_object* v___x_201_; 
lean_dec_ref(v_str_194_);
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
lean_dec_ref(v_e_104_);
v___x_201_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_107_, v_a_108_, v_a_109_, v_a_110_);
return v___x_201_;
}
}
else
{
lean_object* v___x_202_; 
lean_dec_ref_known(v_declName_192_, 2);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_202_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_202_;
}
}
else
{
lean_object* v___x_203_; 
lean_dec(v_declName_192_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_203_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_203_;
}
}
default: 
{
lean_object* v___x_204_; 
lean_dec(v_a_113_);
lean_inc(v_a_110_);
lean_inc_ref(v_a_109_);
lean_inc(v_a_108_);
lean_inc_ref(v_a_107_);
v___x_204_ = lean_apply_7(v_k_106_, v_e_104_, v_F_105_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, lean_box(0));
return v___x_204_;
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec_ref(v_k_106_);
lean_dec_ref(v_F_105_);
lean_dec_ref(v_e_104_);
v_a_205_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_112_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_112_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg___boxed(lean_object* v_e_213_, lean_object* v_F_214_, lean_object* v_k_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_213_, v_F_214_, v_k_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd(lean_object* v_00_u03b1_222_, lean_object* v_e_223_, lean_object* v_F_224_, lean_object* v_k_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_223_, v_F_224_, v_k_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___boxed(lean_object* v_00_u03b1_232_, lean_object* v_e_233_, lean_object* v_F_234_, lean_object* v_k_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Elab_Structural_searchPProd(v_00_u03b1_232_, v_e_233_, v_F_234_, v_k_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(lean_object* v_k_242_, lean_object* v_b_243_, lean_object* v_c_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
lean_inc(v___y_246_);
lean_inc_ref(v___y_245_);
v___x_250_ = lean_apply_7(v_k_242_, v_b_243_, v_c_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, lean_box(0));
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_251_, lean_object* v_b_252_, lean_object* v_c_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(v_k_251_, v_b_252_, v_c_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(lean_object* v_type_260_, lean_object* v_k_261_, uint8_t v_cleanupAnnotations_262_, uint8_t v_whnfType_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___f_269_; lean_object* v___x_270_; 
v___f_269_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_269_, 0, v_k_261_);
v___x_270_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_260_, v___f_269_, v_cleanupAnnotations_262_, v_whnfType_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_270_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_270_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___boxed(lean_object* v_type_287_, lean_object* v_k_288_, lean_object* v_cleanupAnnotations_289_, lean_object* v_whnfType_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_296_; uint8_t v_whnfType_boxed_297_; lean_object* v_res_298_; 
v_cleanupAnnotations_boxed_296_ = lean_unbox(v_cleanupAnnotations_289_);
v_whnfType_boxed_297_ = lean_unbox(v_whnfType_290_);
v_res_298_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_287_, v_k_288_, v_cleanupAnnotations_boxed_296_, v_whnfType_boxed_297_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object* v_00_u03b1_299_, lean_object* v_type_300_, lean_object* v_k_301_, uint8_t v_cleanupAnnotations_302_, uint8_t v_whnfType_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_300_, v_k_301_, v_cleanupAnnotations_302_, v_whnfType_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object* v_00_u03b1_310_, lean_object* v_type_311_, lean_object* v_k_312_, lean_object* v_cleanupAnnotations_313_, lean_object* v_whnfType_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_320_; uint8_t v_whnfType_boxed_321_; lean_object* v_res_322_; 
v_cleanupAnnotations_boxed_320_ = lean_unbox(v_cleanupAnnotations_313_);
v_whnfType_boxed_321_ = lean_unbox(v_whnfType_314_);
v_res_322_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_00_u03b1_310_, v_type_311_, v_k_312_, v_cleanupAnnotations_boxed_320_, v_whnfType_boxed_321_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object* v_cls_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_toCold_332_; lean_object* v_options_333_; uint8_t v_hasTrace_334_; 
v_toCold_332_ = lean_ctor_get(v___y_329_, 0);
v_options_333_ = lean_ctor_get(v_toCold_332_, 2);
v_hasTrace_334_ = lean_ctor_get_uint8(v_options_333_, sizeof(void*)*1);
if (v_hasTrace_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_cls_326_);
v___x_335_ = lean_box(v_hasTrace_334_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
else
{
lean_object* v_inheritedTraceOptions_337_; lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_inheritedTraceOptions_337_ = lean_ctor_get(v_toCold_332_, 11);
v___x_338_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_339_ = l_Lean_Name_append(v___x_338_, v_cls_326_);
v___x_340_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_337_, v_options_333_, v___x_339_);
lean_dec(v___x_339_);
v___x_341_ = lean_box(v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object* v_cls_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_349_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0(void){
_start:
{
lean_object* v___x_350_; double v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = lean_float_of_nat(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object* v_cls_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_ref_362_; lean_object* v___x_363_; lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_409_; 
v_ref_362_ = lean_ctor_get(v___y_359_, 2);
v___x_363_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_409_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_409_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_409_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v_traceState_369_; lean_object* v_env_370_; lean_object* v_nextMacroScope_371_; lean_object* v_ngen_372_; lean_object* v_auxDeclNGen_373_; lean_object* v_cache_374_; lean_object* v_recordedDeps_375_; lean_object* v_messages_376_; lean_object* v_infoState_377_; lean_object* v_snapshotTasks_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_408_; 
v___x_368_ = lean_st_ref_take(v___y_360_);
v_traceState_369_ = lean_ctor_get(v___x_368_, 4);
v_env_370_ = lean_ctor_get(v___x_368_, 0);
v_nextMacroScope_371_ = lean_ctor_get(v___x_368_, 1);
v_ngen_372_ = lean_ctor_get(v___x_368_, 2);
v_auxDeclNGen_373_ = lean_ctor_get(v___x_368_, 3);
v_cache_374_ = lean_ctor_get(v___x_368_, 5);
v_recordedDeps_375_ = lean_ctor_get(v___x_368_, 6);
v_messages_376_ = lean_ctor_get(v___x_368_, 7);
v_infoState_377_ = lean_ctor_get(v___x_368_, 8);
v_snapshotTasks_378_ = lean_ctor_get(v___x_368_, 9);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_408_ == 0)
{
v___x_380_ = v___x_368_;
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_snapshotTasks_378_);
lean_inc(v_infoState_377_);
lean_inc(v_messages_376_);
lean_inc(v_recordedDeps_375_);
lean_inc(v_cache_374_);
lean_inc(v_traceState_369_);
lean_inc(v_auxDeclNGen_373_);
lean_inc(v_ngen_372_);
lean_inc(v_nextMacroScope_371_);
lean_inc(v_env_370_);
lean_dec(v___x_368_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
uint64_t v_tid_382_; lean_object* v_traces_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_407_; 
v_tid_382_ = lean_ctor_get_uint64(v_traceState_369_, sizeof(void*)*1);
v_traces_383_ = lean_ctor_get(v_traceState_369_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_traceState_369_);
if (v_isSharedCheck_407_ == 0)
{
v___x_385_ = v_traceState_369_;
v_isShared_386_ = v_isSharedCheck_407_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_traces_383_);
lean_dec(v_traceState_369_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_407_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_387_; lean_object* v___x_388_; double v___x_389_; uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_387_ = lean_box(0);
v___x_388_ = lean_box(0);
v___x_389_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_390_ = 0;
v___x_391_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_392_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_392_, 0, v_cls_355_);
lean_ctor_set(v___x_392_, 1, v___x_388_);
lean_ctor_set(v___x_392_, 2, v___x_391_);
lean_ctor_set_float(v___x_392_, sizeof(void*)*3, v___x_389_);
lean_ctor_set_float(v___x_392_, sizeof(void*)*3 + 8, v___x_389_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*3 + 16, v___x_390_);
v___x_393_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_394_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v_a_364_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
lean_inc(v_ref_362_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v_ref_362_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_PersistentArray_push___redArg(v_traces_383_, v___x_395_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_396_);
v___x_398_ = v___x_385_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_396_);
lean_ctor_set_uint64(v_reuseFailAlloc_406_, sizeof(void*)*1, v_tid_382_);
v___x_398_ = v_reuseFailAlloc_406_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_400_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 4, v___x_398_);
v___x_400_ = v___x_380_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_env_370_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_nextMacroScope_371_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_ngen_372_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_auxDeclNGen_373_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_405_, 5, v_cache_374_);
lean_ctor_set(v_reuseFailAlloc_405_, 6, v_recordedDeps_375_);
lean_ctor_set(v_reuseFailAlloc_405_, 7, v_messages_376_);
lean_ctor_set(v_reuseFailAlloc_405_, 8, v_infoState_377_);
lean_ctor_set(v_reuseFailAlloc_405_, 9, v_snapshotTasks_378_);
v___x_400_ = v_reuseFailAlloc_405_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_st_ref_put(v___y_360_, v___x_400_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_387_);
v___x_403_ = v___x_366_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_387_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object* v_cls_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_410_, v_msg_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0));
v___x_420_ = l_Lean_stringToMessageData(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2));
v___x_423_ = l_Lean_stringToMessageData(v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v_a_424_, lean_object* v_C_425_, lean_object* v_cls_426_, lean_object* v___f_427_, lean_object* v_belowDict_428_, lean_object* v_F_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___y_436_; lean_object* v___y_437_; lean_object* v___y_438_; lean_object* v___y_439_; lean_object* v___y_440_; lean_object* v___x_504_; 
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_504_ = lean_apply_5(v___f_427_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
goto v___jp_468_;
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_428_);
v___x_508_ = l_Lean_indentExpr(v_belowDict_428_);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
lean_inc(v_cls_426_);
v___x_510_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_426_, v___x_509_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_dec_ref_known(v___x_510_, 1);
goto v___jp_468_;
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_F_429_);
lean_dec_ref(v_belowDict_428_);
lean_dec(v_cls_426_);
lean_dec_ref(v_a_424_);
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
lean_dec_ref(v_F_429_);
lean_dec_ref(v_belowDict_428_);
lean_dec(v_cls_426_);
lean_dec_ref(v_a_424_);
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
v___jp_435_:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_isExprDefEq(v___y_436_, v_a_424_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_459_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_459_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_459_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_459_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
uint8_t v___x_446_; 
v___x_446_ = lean_unbox(v_a_442_);
lean_dec(v_a_442_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_del_object(v___x_444_);
lean_dec_ref(v_F_429_);
v___x_447_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_437_, v___y_438_, v___y_439_, v___y_440_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v___x_457_; 
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v_F_429_);
v___x_457_ = v___x_444_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_F_429_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_dec_ref(v_F_429_);
v_a_460_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_441_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_441_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_465_; 
if (v_isShared_463_ == 0)
{
v___x_465_ = v___x_462_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_460_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
v___jp_468_:
{
if (lean_obj_tag(v_belowDict_428_) == 5)
{
lean_object* v_fn_469_; lean_object* v_arg_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
lean_dec(v_cls_426_);
v_fn_469_ = lean_ctor_get(v_belowDict_428_, 0);
lean_inc_ref(v_fn_469_);
v_arg_470_ = lean_ctor_get(v_belowDict_428_, 1);
lean_inc_ref(v_arg_470_);
lean_dec_ref_known(v_belowDict_428_, 2);
v___x_471_ = l_Lean_Expr_getAppFn(v_fn_469_);
lean_dec_ref(v_fn_469_);
v___x_472_ = lean_expr_eqv(v___x_471_, v_C_425_);
lean_dec_ref(v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec_ref(v_arg_470_);
lean_dec_ref(v_F_429_);
lean_dec_ref(v_a_424_);
v___x_473_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_430_, v___y_431_, v___y_432_, v___y_433_);
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
v___y_436_ = v_arg_470_;
v___y_437_ = v___y_430_;
v___y_438_ = v___y_431_;
v___y_439_ = v___y_432_;
v___y_440_ = v___y_433_;
goto v___jp_435_;
}
}
else
{
lean_object* v_toCold_482_; lean_object* v_options_483_; uint8_t v_hasTrace_484_; 
lean_dec_ref(v_F_429_);
lean_dec_ref(v_a_424_);
v_toCold_482_ = lean_ctor_get(v___y_432_, 0);
v_options_483_ = lean_ctor_get(v_toCold_482_, 2);
v_hasTrace_484_ = lean_ctor_get_uint8(v_options_483_, sizeof(void*)*1);
if (v_hasTrace_484_ == 0)
{
lean_object* v___x_485_; 
lean_dec_ref(v_belowDict_428_);
lean_dec(v_cls_426_);
v___x_485_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_485_;
}
else
{
lean_object* v_inheritedTraceOptions_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_inheritedTraceOptions_486_ = lean_ctor_get(v_toCold_482_, 11);
v___x_487_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_426_);
v___x_488_ = l_Lean_Name_append(v___x_487_, v_cls_426_);
v___x_489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_486_, v_options_483_, v___x_488_);
lean_dec(v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; 
lean_dec_ref(v_belowDict_428_);
lean_dec(v_cls_426_);
v___x_490_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_492_ = l_Lean_indentExpr(v_belowDict_428_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_426_, v___x_493_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v___x_495_; 
lean_dec_ref_known(v___x_494_, 1);
v___x_495_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_430_, v___y_431_, v___y_432_, v___y_433_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v_a_527_, lean_object* v_C_528_, lean_object* v_cls_529_, lean_object* v___f_530_, lean_object* v_belowDict_531_, lean_object* v_F_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v_a_527_, v_C_528_, v_cls_529_, v___f_530_, v_belowDict_531_, v_F_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec_ref(v_C_528_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_541_, lean_object* v_C_542_, lean_object* v_cls_543_, lean_object* v___f_544_, lean_object* v_F_545_, lean_object* v_xs_546_, lean_object* v_belowDict_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
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
lean_closure_set(v___f_556_, 0, v_a_555_);
lean_closure_set(v___f_556_, 1, v_C_542_);
lean_closure_set(v___f_556_, 2, v_cls_543_);
lean_closure_set(v___f_556_, 3, v___f_544_);
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
lean_dec_ref(v___f_544_);
lean_dec(v_cls_543_);
lean_dec_ref(v_C_542_);
return v___x_554_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_587_, lean_object* v_C_588_, lean_object* v_cls_589_, lean_object* v___f_590_, lean_object* v_F_591_, lean_object* v_xs_592_, lean_object* v_belowDict_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_587_, v_C_588_, v_cls_589_, v___f_590_, v_F_591_, v_xs_592_, v_belowDict_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v_arg_603_, lean_object* v_C_604_, lean_object* v_cls_605_, lean_object* v___f_606_, lean_object* v_belowDict_607_, lean_object* v_F_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v___f_614_; lean_object* v___x_618_; 
lean_inc_ref(v___f_606_);
lean_inc(v_cls_605_);
v___f_614_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_614_, 0, v_arg_603_);
lean_closure_set(v___f_614_, 1, v_C_604_);
lean_closure_set(v___f_614_, 2, v_cls_605_);
lean_closure_set(v___f_614_, 3, v___f_606_);
lean_closure_set(v___f_614_, 4, v_F_608_);
lean_inc(v___y_612_);
lean_inc_ref(v___y_611_);
lean_inc(v___y_610_);
lean_inc_ref(v___y_609_);
v___x_618_ = lean_apply_5(v___f_606_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, lean_box(0));
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; uint8_t v___x_620_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = lean_unbox(v_a_619_);
lean_dec(v_a_619_);
if (v___x_620_ == 0)
{
lean_dec(v_cls_605_);
goto v___jp_615_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_621_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_607_);
v___x_622_ = l_Lean_indentExpr(v_belowDict_607_);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_605_, v___x_623_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_dec_ref_known(v___x_624_, 1);
goto v___jp_615_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v___f_614_);
lean_dec_ref(v_belowDict_607_);
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v___f_614_);
lean_dec_ref(v_belowDict_607_);
lean_dec(v_cls_605_);
v_a_633_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_618_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_618_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
v___jp_615_:
{
uint8_t v___x_616_; lean_object* v___x_617_; 
v___x_616_ = 0;
v___x_617_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_607_, v___f_614_, v___x_616_, v___x_616_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v_arg_641_, lean_object* v_C_642_, lean_object* v_cls_643_, lean_object* v___f_644_, lean_object* v_belowDict_645_, lean_object* v_F_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v_arg_641_, v_C_642_, v_cls_643_, v___f_644_, v_belowDict_645_, v_F_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_652_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_668_, lean_object* v_belowDict_669_, lean_object* v_arg_670_, lean_object* v_F_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v_cls_677_; lean_object* v___f_678_; lean_object* v___f_679_; lean_object* v___x_680_; lean_object* v_a_681_; uint8_t v___x_682_; 
v_cls_677_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_678_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
lean_inc_ref(v_arg_670_);
v___f_679_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_679_, 0, v_arg_670_);
lean_closure_set(v___f_679_, 1, v_C_668_);
lean_closure_set(v___f_679_, 2, v_cls_677_);
lean_closure_set(v___f_679_, 3, v___f_678_);
v___x_680_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_677_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_680_);
v___x_682_ = lean_unbox(v_a_681_);
lean_dec(v_a_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec_ref(v_arg_670_);
v___x_683_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_669_, v_F_671_, v___f_679_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_684_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_669_);
v___x_685_ = l_Lean_indentExpr(v_belowDict_669_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_indentExpr(v_arg_670_);
v___x_690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v___x_691_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_677_, v___x_690_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_692_; 
lean_dec_ref_known(v___x_691_, 1);
v___x_692_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_669_, v_F_671_, v___f_679_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_692_;
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec_ref(v___f_679_);
lean_dec_ref(v_F_671_);
lean_dec_ref(v_belowDict_669_);
v_a_693_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_691_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_701_, lean_object* v_belowDict_702_, lean_object* v_arg_703_, lean_object* v_F_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_701_, v_belowDict_702_, v_arg_703_, v_F_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v_t_711_, lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_718_, 0, v_t_711_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v_t_719_, lean_object* v_x_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v_t_719_, v_x_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_x_720_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___f_736_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_736_, 0, v_t_730_);
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1));
v___x_738_ = l_Lean_Core_mkFreshUserName(v___x_737_, v___y_733_, v___y_734_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_747_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_a_739_);
lean_ctor_set(v___x_743_, 1, v___f_736_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___f_736_);
v_a_748_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_738_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_738_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v___x_763_, lean_object* v_a_764_, lean_object* v_x_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_array_set(v___y_766_, v_a_764_, v___x_763_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v___x_775_, lean_object* v_a_776_, lean_object* v_x_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v___x_775_, v_a_776_, v_x_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v_a_776_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_785_, lean_object* v_a_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_snd_794_; lean_object* v_fst_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_846_; 
v_snd_794_ = lean_ctor_get(v___y_788_, 1);
v_fst_795_ = lean_ctor_get(v___y_788_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___y_788_);
if (v_isSharedCheck_846_ == 0)
{
v___x_797_ = v___y_788_;
v_isShared_798_ = v_isSharedCheck_846_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_snd_794_);
lean_inc(v_fst_795_);
lean_dec(v___y_788_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_846_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_array_799_; lean_object* v_start_800_; lean_object* v_stop_801_; uint8_t v___x_802_; 
v_array_799_ = lean_ctor_get(v_snd_794_, 0);
v_start_800_ = lean_ctor_get(v_snd_794_, 1);
v_stop_801_ = lean_ctor_get(v_snd_794_, 2);
v___x_802_ = lean_nat_dec_lt(v_start_800_, v_stop_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_804_; 
lean_dec_ref(v_a_786_);
lean_dec_ref(v___x_785_);
if (v_isShared_798_ == 0)
{
v___x_804_ = v___x_797_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_fst_795_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_snd_794_);
v___x_804_ = v_reuseFailAlloc_807_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
v___x_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
return v___x_806_;
}
}
else
{
lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_842_; 
lean_inc(v_stop_801_);
lean_inc(v_start_800_);
lean_inc_ref(v_array_799_);
v_isSharedCheck_842_ = !lean_is_exclusive(v_snd_794_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; lean_object* v_unused_844_; lean_object* v_unused_845_; 
v_unused_843_ = lean_ctor_get(v_snd_794_, 2);
lean_dec(v_unused_843_);
v_unused_844_ = lean_ctor_get(v_snd_794_, 1);
lean_dec(v_unused_844_);
v_unused_845_ = lean_ctor_get(v_snd_794_, 0);
lean_dec(v_unused_845_);
v___x_809_ = v_snd_794_;
v_isShared_810_ = v_isSharedCheck_842_;
goto v_resetjp_808_;
}
else
{
lean_dec(v_snd_794_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_842_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
v___x_811_ = lean_array_fget_borrowed(v_array_799_, v_start_800_);
lean_inc(v___x_811_);
v___f_812_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_812_, 0, v___x_811_);
v___x_813_ = lean_unsigned_to_nat(1u);
v___x_814_ = lean_nat_add(v_start_800_, v___x_813_);
lean_dec(v_start_800_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v___x_814_);
v___x_816_ = v___x_809_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_array_799_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_841_, 2, v_stop_801_);
v___x_816_ = v_reuseFailAlloc_841_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
size_t v_sz_817_; size_t v___x_818_; lean_object* v___x_9002__overap_819_; lean_object* v___x_820_; 
v_sz_817_ = lean_array_size(v_a_786_);
v___x_818_ = ((size_t)0ULL);
v___x_9002__overap_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_785_, v_a_786_, v___f_812_, v_sz_817_, v___x_818_, v_fst_795_);
lean_inc(v___y_792_);
lean_inc_ref(v___y_791_);
lean_inc(v___y_790_);
lean_inc_ref(v___y_789_);
v___x_820_ = lean_apply_5(v___x_9002__overap_819_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, lean_box(0));
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_832_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_832_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_832_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___x_816_);
lean_ctor_set(v___x_797_, 0, v_a_821_);
v___x_826_ = v___x_797_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_821_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_816_);
v___x_826_ = v_reuseFailAlloc_831_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 0, v___x_827_);
v___x_829_ = v___x_823_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref(v___x_816_);
lean_del_object(v___x_797_);
v_a_833_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_820_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_820_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_847_, lean_object* v_a_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_847_, v_a_848_, v_x_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_toCold_863_; lean_object* v_options_864_; uint8_t v_hasTrace_865_; 
v_toCold_863_ = lean_ctor_get(v___y_860_, 0);
v_options_864_ = lean_ctor_get(v_toCold_863_, 2);
v_hasTrace_865_ = lean_ctor_get_uint8(v_options_864_, sizeof(void*)*1);
if (v_hasTrace_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v___x_857_);
v___x_866_ = lean_box(v_hasTrace_865_);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
else
{
lean_object* v_inheritedTraceOptions_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_inheritedTraceOptions_868_ = lean_ctor_get(v_toCold_863_, 11);
v___x_869_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_870_ = l_Lean_Name_append(v___x_869_, v___x_857_);
v___x_871_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_868_, v_options_864_, v___x_870_);
lean_dec(v___x_870_);
v___x_872_ = lean_box(v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_880_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_891_ = l_Lean_stringToMessageData(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v_positions_894_, lean_object* v_a_895_, lean_object* v___x_896_, lean_object* v___x_897_, lean_object* v_k_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v_toMonadRef_901_, lean_object* v___x_902_, lean_object* v___f_903_, lean_object* v_Cs_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_9038__overap_911_; lean_object* v___x_912_; 
v___x_910_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_904_);
lean_inc_ref(v___x_892_);
v___x_9038__overap_911_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_892_, v___x_893_, v___x_910_, v_positions_894_, v_a_895_, v_Cs_904_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
v___x_912_ = lean_apply_5(v___x_9038__overap_911_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, lean_box(0));
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___x_956_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = l_Lean_mkAppN(v___x_896_, v_a_913_);
lean_dec(v_a_913_);
v___x_915_ = l_Subarray_copy___redArg(v___x_897_);
v___x_916_ = l_Lean_mkAppN(v___x_914_, v___x_915_);
lean_dec_ref(v___x_915_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
v___x_956_ = lean_apply_5(v___f_903_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, lean_box(0));
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; uint8_t v___x_958_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref_known(v___x_956_, 1);
v___x_958_ = lean_unbox(v_a_957_);
lean_dec(v_a_957_);
if (v___x_958_ == 0)
{
v___y_918_ = v___y_905_;
v___y_919_ = v___y_906_;
v___y_920_ = v___y_907_;
v___y_921_ = v___y_908_;
goto v___jp_917_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_9089__overap_970_; lean_object* v___x_971_; 
v___x_959_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_904_);
v___x_960_ = lean_array_to_list(v_Cs_904_);
v___x_961_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_962_ = lean_box(0);
v___x_963_ = l_List_mapTR_loop___redArg(v___x_961_, v___x_960_, v___x_962_);
v___x_964_ = l_Lean_MessageData_ofList(v___x_963_);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_959_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
lean_inc_ref(v___x_916_);
v___x_968_ = l_Lean_indentExpr(v___x_916_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_inc(v___x_899_);
lean_inc_ref(v___x_902_);
lean_inc_ref(v_toMonadRef_901_);
lean_inc_ref(v___x_900_);
lean_inc_ref(v___x_892_);
v___x_9089__overap_970_ = l_Lean_addTrace___redArg(v___x_892_, v___x_900_, v_toMonadRef_901_, v___x_902_, v___x_899_, v___x_969_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
v___x_971_ = lean_apply_5(v___x_9089__overap_970_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, lean_box(0));
if (lean_obj_tag(v___x_971_) == 0)
{
lean_dec_ref_known(v___x_971_, 1);
v___y_918_ = v___y_905_;
v___y_919_ = v___y_906_;
v___y_920_ = v___y_907_;
v___y_921_ = v___y_908_;
goto v___jp_917_;
}
else
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_979_; 
lean_dec_ref(v___x_916_);
lean_dec_ref(v_Cs_904_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v_k_898_);
lean_dec_ref(v___x_892_);
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_979_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_979_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_977_; 
if (v_isShared_975_ == 0)
{
v___x_977_ = v___x_974_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v_a_972_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v___x_916_);
lean_dec_ref(v_Cs_904_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v_k_898_);
lean_dec_ref(v___x_892_);
v_a_980_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_956_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_956_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
v___jp_917_:
{
lean_object* v_toCold_922_; lean_object* v_options_923_; uint8_t v_hasTrace_924_; 
v_toCold_922_ = lean_ctor_get(v___y_920_, 0);
v_options_923_ = lean_ctor_get(v_toCold_922_, 2);
v_hasTrace_924_ = lean_ctor_get_uint8(v_options_923_, sizeof(void*)*1);
if (v_hasTrace_924_ == 0)
{
lean_object* v___x_925_; 
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v___x_892_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_925_ = lean_apply_7(v_k_898_, v_Cs_904_, v___x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_925_;
}
else
{
lean_object* v_inheritedTraceOptions_926_; lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_inheritedTraceOptions_926_ = lean_ctor_get(v_toCold_922_, 11);
v___x_927_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_899_);
v___x_928_ = l_Lean_Name_append(v___x_927_, v___x_899_);
v___x_929_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_926_, v_options_923_, v___x_928_);
lean_dec(v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v___x_892_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_930_ = lean_apply_7(v_k_898_, v_Cs_904_, v___x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_930_;
}
else
{
lean_object* v___x_931_; 
lean_inc_ref(v___x_916_);
v___x_931_ = l_Lean_Meta_isTypeCorrect(v___x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; uint8_t v___x_933_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
lean_inc(v_a_932_);
lean_dec_ref_known(v___x_931_, 1);
v___x_933_ = lean_unbox(v_a_932_);
lean_dec(v_a_932_);
if (v___x_933_ == 0)
{
if (v___x_929_ == 0)
{
lean_object* v___x_934_; 
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v___x_892_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_934_ = lean_apply_7(v_k_898_, v_Cs_904_, v___x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_9062__overap_936_; lean_object* v___x_937_; 
v___x_935_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_9062__overap_936_ = l_Lean_addTrace___redArg(v___x_892_, v___x_900_, v_toMonadRef_901_, v___x_902_, v___x_899_, v___x_935_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_937_ = lean_apply_5(v___x_9062__overap_936_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; 
lean_dec_ref_known(v___x_937_, 1);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_938_ = lean_apply_7(v_k_898_, v_Cs_904_, v___x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_938_;
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec_ref(v___x_916_);
lean_dec_ref(v_Cs_904_);
lean_dec_ref(v_k_898_);
v_a_939_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_937_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_937_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
else
{
lean_object* v___x_947_; 
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v___x_892_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_947_ = lean_apply_7(v_k_898_, v_Cs_904_, v___x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_947_;
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
lean_dec_ref(v___x_916_);
lean_dec_ref(v_Cs_904_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v_k_898_);
lean_dec_ref(v___x_892_);
v_a_948_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_931_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_931_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v_Cs_904_);
lean_dec_ref(v___f_903_);
lean_dec_ref(v___x_902_);
lean_dec_ref(v_toMonadRef_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec_ref(v_k_898_);
lean_dec_ref(v___x_897_);
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_892_);
v_a_988_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_912_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_912_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_996_ = _args[0];
lean_object* v___x_997_ = _args[1];
lean_object* v_positions_998_ = _args[2];
lean_object* v_a_999_ = _args[3];
lean_object* v___x_1000_ = _args[4];
lean_object* v___x_1001_ = _args[5];
lean_object* v_k_1002_ = _args[6];
lean_object* v___x_1003_ = _args[7];
lean_object* v___x_1004_ = _args[8];
lean_object* v_toMonadRef_1005_ = _args[9];
lean_object* v___x_1006_ = _args[10];
lean_object* v___f_1007_ = _args[11];
lean_object* v_Cs_1008_ = _args[12];
lean_object* v___y_1009_ = _args[13];
lean_object* v___y_1010_ = _args[14];
lean_object* v___y_1011_ = _args[15];
lean_object* v___y_1012_ = _args[16];
lean_object* v___y_1013_ = _args[17];
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_996_, v___x_997_, v_positions_998_, v_a_999_, v___x_1000_, v___x_1001_, v_k_1002_, v___x_1003_, v___x_1004_, v_toMonadRef_1005_, v___x_1006_, v___f_1007_, v_Cs_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
return v_res_1014_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_unsigned_to_nat(37u);
v___x_1016_ = l_Lean_Level_ofNat(v___x_1015_);
return v___x_1016_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1017_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1018_ = l_Lean_Expr_sort___override(v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1025_, lean_object* v___x_1026_, lean_object* v___f_1027_, lean_object* v___f_1028_, lean_object* v___x_1029_, lean_object* v_numTypeFormers_1030_, lean_object* v___x_1031_, lean_object* v_k_1032_, lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v_toMonadRef_1035_, lean_object* v___x_1036_, lean_object* v___f_1037_, lean_object* v_numIndParams_1038_, lean_object* v_a_1039_, lean_object* v_f_1040_, lean_object* v_args_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1054_; lean_object* v___y_1055_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v_lower_1097_; lean_object* v_upper_1098_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___x_1164_; lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1164_ = lean_nat_add(v_numIndParams_1038_, v_numTypeFormers_1030_);
v___x_1165_ = lean_array_get_size(v_args_1041_);
v___x_1166_ = lean_nat_dec_lt(v___x_1164_, v___x_1165_);
lean_dec(v___x_1164_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
lean_dec_ref(v_args_1041_);
lean_dec_ref(v_f_1040_);
lean_dec(v_numIndParams_1038_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v___x_1031_);
lean_dec(v_numTypeFormers_1030_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___f_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v_positions_1025_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
v___x_1167_ = lean_apply_5(v___f_1037_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, lean_box(0));
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; uint8_t v___x_1169_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v___x_1169_ = lean_unbox(v_a_1168_);
lean_dec(v_a_1168_);
if (v___x_1169_ == 0)
{
lean_dec_ref(v_a_1039_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v___x_1026_);
v___y_1151_ = v___y_1042_;
v___y_1152_ = v___y_1043_;
v___y_1153_ = v___y_1044_;
v___y_1154_ = v___y_1045_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_9218__overap_1173_; lean_object* v___x_1174_; 
v___x_1170_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1171_ = l_Lean_indentExpr(v_a_1039_);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_9218__overap_1173_ = l_Lean_addTrace___redArg(v___x_1026_, v___x_1034_, v_toMonadRef_1035_, v___x_1036_, v___x_1033_, v___x_1172_);
lean_inc(v___y_1045_);
lean_inc_ref(v___y_1044_);
lean_inc(v___y_1043_);
lean_inc_ref(v___y_1042_);
v___x_1174_ = lean_apply_5(v___x_9218__overap_1173_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, lean_box(0));
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_dec_ref_known(v___x_1174_, 1);
v___y_1151_ = v___y_1042_;
v___y_1152_ = v___y_1043_;
v___y_1153_ = v___y_1044_;
v___y_1154_ = v___y_1045_;
goto v___jp_1150_;
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1174_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec_ref(v_a_1039_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v___x_1026_);
v_a_1183_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1167_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1167_);
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
else
{
lean_dec_ref(v_a_1039_);
v___y_1141_ = v___y_1042_;
v___y_1142_ = v___y_1043_;
v___y_1143_ = v___y_1044_;
v___y_1144_ = v___y_1045_;
goto v___jp_1140_;
}
v___jp_1047_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; size_t v_sz_1061_; size_t v___x_1062_; lean_object* v___x_9134__overap_1063_; lean_object* v___x_1064_; 
v___x_1056_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1057_ = lean_mk_array(v___y_1051_, v___x_1056_);
v___x_1058_ = lean_array_get_size(v___y_1049_);
v___x_1059_ = l_Array_toSubarray___redArg(v___y_1049_, v___y_1048_, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1057_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v_sz_1061_ = lean_array_size(v_positions_1025_);
v___x_1062_ = ((size_t)0ULL);
lean_inc_ref(v___x_1026_);
v___x_9134__overap_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1026_, v_positions_1025_, v___f_1027_, v_sz_1061_, v___x_1062_, v___x_1060_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
v___x_1064_ = lean_apply_5(v___x_9134__overap_1063_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, lean_box(0));
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v_fst_1066_; size_t v_sz_1067_; lean_object* v___x_9137__overap_1068_; lean_object* v___x_1069_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v_fst_1066_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_fst_1066_);
lean_dec(v_a_1065_);
v_sz_1067_ = lean_array_size(v_fst_1066_);
lean_inc_ref(v___x_1026_);
v___x_9137__overap_1068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1026_, v___f_1028_, v_sz_1067_, v___x_1062_, v_fst_1066_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
v___x_1069_ = lean_apply_5(v___x_9137__overap_1068_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, lean_box(0));
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; uint8_t v___x_1071_; lean_object* v___x_9141__overap_1072_; lean_object* v___x_1073_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1071_ = 0;
v___x_9141__overap_1072_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1029_, v___x_1026_, v_a_1070_, v___y_1050_, v___x_1071_);
lean_inc(v___y_1055_);
lean_inc_ref(v___y_1054_);
lean_inc(v___y_1053_);
lean_inc_ref(v___y_1052_);
v___x_1073_ = lean_apply_5(v___x_9141__overap_1072_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, lean_box(0));
return v___x_1073_;
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v___y_1050_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___x_1026_);
v_a_1074_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1069_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1069_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_dec_ref(v___y_1050_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___f_1028_);
lean_dec_ref(v___x_1026_);
v_a_1082_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1064_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1064_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
v___jp_1090_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1099_ = l_Array_toSubarray___redArg(v_args_1041_, v_lower_1097_, v_upper_1098_);
v___x_1100_ = l_Subarray_copy___redArg(v___y_1091_);
v___x_1101_ = l_Lean_mkAppN(v_f_1040_, v___x_1100_);
lean_dec_ref(v___x_1100_);
lean_inc_ref(v___x_1101_);
v___x_1102_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1030_, v___x_1101_, v___y_1096_, v___y_1092_, v___y_1095_, v___y_1094_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc_n(v_a_1103_, 2);
lean_dec_ref_known(v___x_1102_, 1);
lean_inc_ref(v___f_1037_);
lean_inc_ref(v___x_1036_);
lean_inc_ref(v_toMonadRef_1035_);
lean_inc_ref(v___x_1034_);
lean_inc(v___x_1033_);
lean_inc_ref(v_positions_1025_);
lean_inc_ref(v___x_1026_);
v___f_1104_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1104_, 0, v___x_1026_);
lean_closure_set(v___f_1104_, 1, v___x_1031_);
lean_closure_set(v___f_1104_, 2, v_positions_1025_);
lean_closure_set(v___f_1104_, 3, v_a_1103_);
lean_closure_set(v___f_1104_, 4, v___x_1101_);
lean_closure_set(v___f_1104_, 5, v___x_1099_);
lean_closure_set(v___f_1104_, 6, v_k_1032_);
lean_closure_set(v___f_1104_, 7, v___x_1033_);
lean_closure_set(v___f_1104_, 8, v___x_1034_);
lean_closure_set(v___f_1104_, 9, v_toMonadRef_1035_);
lean_closure_set(v___f_1104_, 10, v___x_1036_);
lean_closure_set(v___f_1104_, 11, v___f_1037_);
v___x_1105_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1025_);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1095_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1096_);
v___x_1106_ = lean_apply_5(v___f_1037_, v___y_1096_, v___y_1092_, v___y_1095_, v___y_1094_, lean_box(0));
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; uint8_t v___x_1108_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
v___x_1108_ = lean_unbox(v_a_1107_);
lean_dec(v_a_1107_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
v___y_1048_ = v___y_1093_;
v___y_1049_ = v_a_1103_;
v___y_1050_ = v___f_1104_;
v___y_1051_ = v___x_1105_;
v___y_1052_ = v___y_1096_;
v___y_1053_ = v___y_1092_;
v___y_1054_ = v___y_1095_;
v___y_1055_ = v___y_1094_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_9173__overap_1114_; lean_object* v___x_1115_; 
v___x_1109_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1105_);
v___x_1110_ = l_Nat_reprFast(v___x_1105_);
v___x_1111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
v___x_1112_ = l_Lean_MessageData_ofFormat(v___x_1111_);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1109_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
lean_inc_ref(v___x_1026_);
v___x_9173__overap_1114_ = l_Lean_addTrace___redArg(v___x_1026_, v___x_1034_, v_toMonadRef_1035_, v___x_1036_, v___x_1033_, v___x_1113_);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1095_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1096_);
v___x_1115_ = lean_apply_5(v___x_9173__overap_1114_, v___y_1096_, v___y_1092_, v___y_1095_, v___y_1094_, lean_box(0));
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_dec_ref_known(v___x_1115_, 1);
v___y_1048_ = v___y_1093_;
v___y_1049_ = v_a_1103_;
v___y_1050_ = v___f_1104_;
v___y_1051_ = v___x_1105_;
v___y_1052_ = v___y_1096_;
v___y_1053_ = v___y_1092_;
v___y_1054_ = v___y_1095_;
v___y_1055_ = v___y_1094_;
goto v___jp_1047_;
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec(v___x_1105_);
lean_dec_ref(v___f_1104_);
lean_dec(v_a_1103_);
lean_dec(v___y_1093_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___f_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_positions_1025_);
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1115_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1115_);
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
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v___x_1105_);
lean_dec_ref(v___f_1104_);
lean_dec(v_a_1103_);
lean_dec(v___y_1093_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___f_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_positions_1025_);
v_a_1124_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1106_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1106_);
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
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v___x_1101_);
lean_dec_ref(v___x_1099_);
lean_dec(v___y_1093_);
lean_dec_ref(v___f_1037_);
lean_dec_ref(v___x_1036_);
lean_dec_ref(v_toMonadRef_1035_);
lean_dec_ref(v___x_1034_);
lean_dec(v___x_1033_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v___x_1031_);
lean_dec_ref(v___x_1029_);
lean_dec_ref(v___f_1028_);
lean_dec_ref(v___f_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_positions_1025_);
v_a_1132_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1102_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1102_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
v___jp_1140_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1145_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1038_);
lean_inc_ref(v_args_1041_);
v___x_1146_ = l_Array_toSubarray___redArg(v_args_1041_, v___x_1145_, v_numIndParams_1038_);
v___x_1147_ = lean_nat_add(v_numIndParams_1038_, v_numTypeFormers_1030_);
lean_dec(v_numIndParams_1038_);
v___x_1148_ = lean_array_get_size(v_args_1041_);
v___x_1149_ = lean_nat_dec_le(v___x_1147_, v___x_1145_);
if (v___x_1149_ == 0)
{
v___y_1091_ = v___x_1146_;
v___y_1092_ = v___y_1142_;
v___y_1093_ = v___x_1145_;
v___y_1094_ = v___y_1144_;
v___y_1095_ = v___y_1143_;
v___y_1096_ = v___y_1141_;
v_lower_1097_ = v___x_1147_;
v_upper_1098_ = v___x_1148_;
goto v___jp_1090_;
}
else
{
lean_dec(v___x_1147_);
v___y_1091_ = v___x_1146_;
v___y_1092_ = v___y_1142_;
v___y_1093_ = v___x_1145_;
v___y_1094_ = v___y_1144_;
v___y_1095_ = v___y_1143_;
v___y_1096_ = v___y_1141_;
v_lower_1097_ = v___x_1145_;
v_upper_1098_ = v___x_1148_;
goto v___jp_1090_;
}
}
v___jp_1150_:
{
lean_object* v___x_1155_; lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v___x_1155_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1155_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1155_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1155_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1191_ = _args[0];
lean_object* v___x_1192_ = _args[1];
lean_object* v___f_1193_ = _args[2];
lean_object* v___f_1194_ = _args[3];
lean_object* v___x_1195_ = _args[4];
lean_object* v_numTypeFormers_1196_ = _args[5];
lean_object* v___x_1197_ = _args[6];
lean_object* v_k_1198_ = _args[7];
lean_object* v___x_1199_ = _args[8];
lean_object* v___x_1200_ = _args[9];
lean_object* v_toMonadRef_1201_ = _args[10];
lean_object* v___x_1202_ = _args[11];
lean_object* v___f_1203_ = _args[12];
lean_object* v_numIndParams_1204_ = _args[13];
lean_object* v_a_1205_ = _args[14];
lean_object* v_f_1206_ = _args[15];
lean_object* v_args_1207_ = _args[16];
lean_object* v___y_1208_ = _args[17];
lean_object* v___y_1209_ = _args[18];
lean_object* v___y_1210_ = _args[19];
lean_object* v___y_1211_ = _args[20];
lean_object* v___y_1212_ = _args[21];
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1191_, v___x_1192_, v___f_1193_, v___f_1194_, v___x_1195_, v_numTypeFormers_1196_, v___x_1197_, v_k_1198_, v___x_1199_, v___x_1200_, v_toMonadRef_1201_, v___x_1202_, v___f_1203_, v_numIndParams_1204_, v_a_1205_, v_f_1206_, v_args_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
return v_res_1213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = l_instMonadEIO___redArg();
return v___x_1214_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1216_ = l_StateRefT_x27_instMonad___redArg(v___x_1215_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1225_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___f_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1228_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1227_, v___x_1226_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1232_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1234_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1233_, v___x_1232_, v___x_1231_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___f_1237_; lean_object* v___x_1238_; 
v___x_1235_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1238_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1237_, v___f_1236_, v___x_1235_);
return v___x_1238_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1243_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1244_ = l_Lean_Name_append(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17));
v___x_1247_ = l_Lean_stringToMessageData(v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1248_, lean_object* v_numIndParams_1249_, lean_object* v_positions_1250_, lean_object* v_k_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v___x_1257_; lean_object* v_toApplicative_1258_; lean_object* v_toFunctor_1259_; lean_object* v_toSeq_1260_; lean_object* v_toSeqLeft_1261_; lean_object* v_toSeqRight_1262_; lean_object* v___f_1263_; lean_object* v___f_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v_toApplicative_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1402_; 
v___x_1257_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1258_ = lean_ctor_get(v___x_1257_, 0);
v_toFunctor_1259_ = lean_ctor_get(v_toApplicative_1258_, 0);
v_toSeq_1260_ = lean_ctor_get(v_toApplicative_1258_, 2);
v_toSeqLeft_1261_ = lean_ctor_get(v_toApplicative_1258_, 3);
v_toSeqRight_1262_ = lean_ctor_get(v_toApplicative_1258_, 4);
v___f_1263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1264_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1259_, 2);
v___f_1265_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1265_, 0, v_toFunctor_1259_);
v___f_1266_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1266_, 0, v_toFunctor_1259_);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___f_1265_);
lean_ctor_set(v___x_1267_, 1, v___f_1266_);
lean_inc(v_toSeqRight_1262_);
v___f_1268_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1268_, 0, v_toSeqRight_1262_);
lean_inc(v_toSeqLeft_1261_);
v___f_1269_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1269_, 0, v_toSeqLeft_1261_);
lean_inc(v_toSeq_1260_);
v___f_1270_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1270_, 0, v_toSeq_1260_);
v___x_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1267_);
lean_ctor_set(v___x_1271_, 1, v___f_1263_);
lean_ctor_set(v___x_1271_, 2, v___f_1270_);
lean_ctor_set(v___x_1271_, 3, v___f_1269_);
lean_ctor_set(v___x_1271_, 4, v___f_1268_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set(v___x_1272_, 1, v___f_1264_);
v___x_1273_ = l_StateRefT_x27_instMonad___redArg(v___x_1272_);
v_toApplicative_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1273_, 1);
lean_dec(v_unused_1403_);
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1402_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_toApplicative_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1402_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v_toFunctor_1278_; lean_object* v_toSeq_1279_; lean_object* v_toSeqLeft_1280_; lean_object* v_toSeqRight_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1400_; 
v_toFunctor_1278_ = lean_ctor_get(v_toApplicative_1274_, 0);
v_toSeq_1279_ = lean_ctor_get(v_toApplicative_1274_, 2);
v_toSeqLeft_1280_ = lean_ctor_get(v_toApplicative_1274_, 3);
v_toSeqRight_1281_ = lean_ctor_get(v_toApplicative_1274_, 4);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_toApplicative_1274_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v_toApplicative_1274_, 1);
lean_dec(v_unused_1401_);
v___x_1283_ = v_toApplicative_1274_;
v_isShared_1284_ = v_isSharedCheck_1400_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_toSeqRight_1281_);
lean_inc(v_toSeqLeft_1280_);
lean_inc(v_toSeq_1279_);
lean_inc(v_toFunctor_1278_);
lean_dec(v_toApplicative_1274_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1400_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___f_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___x_1294_; 
v___f_1285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1286_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1278_);
v___f_1287_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1287_, 0, v_toFunctor_1278_);
v___f_1288_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1288_, 0, v_toFunctor_1278_);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___f_1287_);
lean_ctor_set(v___x_1289_, 1, v___f_1288_);
v___f_1290_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1290_, 0, v_toSeqRight_1281_);
v___f_1291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1291_, 0, v_toSeqLeft_1280_);
v___f_1292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1292_, 0, v_toSeq_1279_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 4, v___f_1290_);
lean_ctor_set(v___x_1283_, 3, v___f_1291_);
lean_ctor_set(v___x_1283_, 2, v___f_1292_);
lean_ctor_set(v___x_1283_, 1, v___f_1285_);
lean_ctor_set(v___x_1283_, 0, v___x_1289_);
v___x_1294_ = v___x_1283_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___f_1285_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v___f_1292_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v___f_1291_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v___f_1290_);
v___x_1294_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1296_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___f_1286_);
lean_ctor_set(v___x_1276_, 0, v___x_1294_);
v___x_1296_ = v___x_1276_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1294_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v___f_1286_);
v___x_1296_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; lean_object* v_toApplicative_1298_; lean_object* v_toFunctor_1299_; lean_object* v_toSeq_1300_; lean_object* v_toSeqLeft_1301_; lean_object* v_toSeqRight_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_toMonadRef_1315_; lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_numTypeFormers_1320_; lean_object* v___x_1321_; 
v___x_1297_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1298_ = lean_ctor_get(v___x_1257_, 0);
v_toFunctor_1299_ = lean_ctor_get(v_toApplicative_1298_, 0);
v_toSeq_1300_ = lean_ctor_get(v_toApplicative_1298_, 2);
v_toSeqLeft_1301_ = lean_ctor_get(v_toApplicative_1298_, 3);
v_toSeqRight_1302_ = lean_ctor_get(v_toApplicative_1298_, 4);
lean_inc_ref_n(v_toFunctor_1299_, 2);
v___f_1303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1303_, 0, v_toFunctor_1299_);
v___f_1304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1304_, 0, v_toFunctor_1299_);
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___f_1303_);
lean_ctor_set(v___x_1305_, 1, v___f_1304_);
lean_inc(v_toSeqRight_1302_);
v___f_1306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1306_, 0, v_toSeqRight_1302_);
lean_inc(v_toSeqLeft_1301_);
v___f_1307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1307_, 0, v_toSeqLeft_1301_);
lean_inc(v_toSeq_1300_);
v___f_1308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1308_, 0, v_toSeq_1300_);
v___x_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1305_);
lean_ctor_set(v___x_1309_, 1, v___f_1263_);
lean_ctor_set(v___x_1309_, 2, v___f_1308_);
lean_ctor_set(v___x_1309_, 3, v___f_1307_);
lean_ctor_set(v___x_1309_, 4, v___f_1306_);
v___x_1310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v___f_1264_);
v___x_1311_ = l_StateRefT_x27_instMonad___redArg(v___x_1310_);
v___x_1312_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1312_, 0, lean_box(0));
lean_closure_set(v___x_1312_, 1, lean_box(0));
lean_closure_set(v___x_1312_, 2, v___x_1311_);
v___x_1313_ = l_instMonadControlTOfPure___redArg(v___x_1312_);
v___x_1314_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1315_ = lean_ctor_get(v___x_1314_, 0);
v___f_1316_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
lean_inc_ref(v___x_1296_);
v___f_1317_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_1317_, 0, v___x_1296_);
v___x_1318_ = l_Lean_instInhabitedExpr;
v___x_1319_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1320_ = lean_array_get_size(v_positions_1250_);
lean_inc(v_a_1255_);
lean_inc_ref(v_a_1254_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
lean_inc_ref(v_below_1248_);
v___x_1321_ = lean_infer_type(v_below_1248_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___f_1324_; lean_object* v___f_1325_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___x_1374_; lean_object* v_a_1375_; uint8_t v___x_1376_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_n(v_a_1322_, 2);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref(v_toMonadRef_1315_);
lean_inc_ref(v___x_1296_);
v___f_1325_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1325_, 0, v_positions_1250_);
lean_closure_set(v___f_1325_, 1, v___x_1296_);
lean_closure_set(v___f_1325_, 2, v___f_1317_);
lean_closure_set(v___f_1325_, 3, v___f_1316_);
lean_closure_set(v___f_1325_, 4, v___x_1313_);
lean_closure_set(v___f_1325_, 5, v_numTypeFormers_1320_);
lean_closure_set(v___f_1325_, 6, v___x_1318_);
lean_closure_set(v___f_1325_, 7, v_k_1251_);
lean_closure_set(v___f_1325_, 8, v___x_1323_);
lean_closure_set(v___f_1325_, 9, v___x_1297_);
lean_closure_set(v___f_1325_, 10, v_toMonadRef_1315_);
lean_closure_set(v___f_1325_, 11, v___x_1319_);
lean_closure_set(v___f_1325_, 12, v___f_1324_);
lean_closure_set(v___f_1325_, 13, v_numIndParams_1249_);
lean_closure_set(v___f_1325_, 14, v_a_1322_);
v___x_1374_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1323_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref(v___x_1374_);
v___x_1376_ = lean_unbox(v_a_1375_);
lean_dec(v_a_1375_);
if (v___x_1376_ == 0)
{
v___y_1339_ = v_a_1252_;
v___y_1340_ = v_a_1253_;
v___y_1341_ = v_a_1254_;
v___y_1342_ = v_a_1255_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_8829__overap_1380_; lean_object* v___x_1381_; 
v___x_1377_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18);
lean_inc(v_a_1322_);
v___x_1378_ = l_Lean_MessageData_ofExpr(v_a_1322_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
lean_inc_ref(v_toMonadRef_1315_);
lean_inc_ref(v___x_1296_);
v___x_8829__overap_1380_ = l_Lean_addTrace___redArg(v___x_1296_, v___x_1297_, v_toMonadRef_1315_, v___x_1319_, v___x_1323_, v___x_1379_);
lean_inc(v_a_1255_);
lean_inc_ref(v_a_1254_);
lean_inc(v_a_1253_);
lean_inc_ref(v_a_1252_);
v___x_1381_ = lean_apply_5(v___x_8829__overap_1380_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, lean_box(0));
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_dec_ref_known(v___x_1381_, 1);
v___y_1339_ = v_a_1252_;
v___y_1340_ = v_a_1253_;
v___y_1341_ = v_a_1254_;
v___y_1342_ = v_a_1255_;
goto v___jp_1338_;
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v___f_1325_);
lean_dec(v_a_1322_);
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_below_1248_);
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1381_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1381_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
v___jp_1326_:
{
lean_object* v_dummy_1331_; lean_object* v_nargs_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_8825__overap_1336_; lean_object* v___x_1337_; 
v_dummy_1331_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1332_ = l_Lean_Expr_getAppNumArgs(v_a_1322_);
lean_inc(v_nargs_1332_);
v___x_1333_ = lean_mk_array(v_nargs_1332_, v_dummy_1331_);
v___x_1334_ = lean_unsigned_to_nat(1u);
v___x_1335_ = lean_nat_sub(v_nargs_1332_, v___x_1334_);
lean_dec(v_nargs_1332_);
v___x_8825__overap_1336_ = l_Lean_Expr_withAppAux___redArg(v___f_1325_, v_a_1322_, v___x_1333_, v___x_1335_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
v___x_1337_ = lean_apply_5(v___x_8825__overap_1336_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, lean_box(0));
return v___x_1337_;
}
v___jp_1338_:
{
lean_object* v_toCold_1343_; lean_object* v_options_1344_; uint8_t v_hasTrace_1345_; 
v_toCold_1343_ = lean_ctor_get(v___y_1341_, 0);
v_options_1344_ = lean_ctor_get(v_toCold_1343_, 2);
v_hasTrace_1345_ = lean_ctor_get_uint8(v_options_1344_, sizeof(void*)*1);
if (v_hasTrace_1345_ == 0)
{
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_below_1248_);
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
v___y_1329_ = v___y_1341_;
v___y_1330_ = v___y_1342_;
goto v___jp_1326_;
}
else
{
lean_object* v_inheritedTraceOptions_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_inheritedTraceOptions_1346_ = lean_ctor_get(v_toCold_1343_, 11);
v___x_1347_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1346_, v_options_1344_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_below_1248_);
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
v___y_1329_ = v___y_1341_;
v___y_1330_ = v___y_1342_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_Meta_isTypeCorrect(v_below_1248_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; uint8_t v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = lean_unbox(v_a_1350_);
lean_dec(v_a_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v_a_1353_; uint8_t v___x_1354_; 
v___x_1352_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1323_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = lean_unbox(v_a_1353_);
lean_dec(v_a_1353_);
if (v___x_1354_ == 0)
{
lean_dec_ref(v___x_1296_);
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
v___y_1329_ = v___y_1341_;
v___y_1330_ = v___y_1342_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_8827__overap_1356_; lean_object* v___x_1357_; 
v___x_1355_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1315_);
v___x_8827__overap_1356_ = l_Lean_addTrace___redArg(v___x_1296_, v___x_1297_, v_toMonadRef_1315_, v___x_1319_, v___x_1323_, v___x_1355_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
v___x_1357_ = lean_apply_5(v___x_8827__overap_1356_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, lean_box(0));
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
v___y_1329_ = v___y_1341_;
v___y_1330_ = v___y_1342_;
goto v___jp_1326_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v___f_1325_);
lean_dec(v_a_1322_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1296_);
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1340_;
v___y_1329_ = v___y_1341_;
v___y_1330_ = v___y_1342_;
goto v___jp_1326_;
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v___f_1325_);
lean_dec(v_a_1322_);
lean_dec_ref(v___x_1296_);
v_a_1366_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1349_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1349_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1397_; 
lean_dec_ref(v___f_1317_);
lean_dec_ref(v___x_1313_);
lean_dec_ref(v___x_1296_);
lean_dec_ref(v_k_1251_);
lean_dec_ref(v_positions_1250_);
lean_dec(v_numIndParams_1249_);
lean_dec_ref(v_below_1248_);
v_a_1390_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1392_ = v___x_1321_;
v_isShared_1393_ = v_isSharedCheck_1397_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1321_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1404_, lean_object* v_numIndParams_1405_, lean_object* v_positions_1406_, lean_object* v_k_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1404_, v_numIndParams_1405_, v_positions_1406_, v_k_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1414_, lean_object* v_inst_1415_, lean_object* v_below_1416_, lean_object* v_numIndParams_1417_, lean_object* v_positions_1418_, lean_object* v_k_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1416_, v_numIndParams_1417_, v_positions_1418_, v_k_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_inst_1427_, lean_object* v_below_1428_, lean_object* v_numIndParams_1429_, lean_object* v_positions_1430_, lean_object* v_k_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1426_, v_inst_1427_, v_below_1428_, v_numIndParams_1429_, v_positions_1430_, v_k_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_inst_1427_);
return v_res_1437_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_unsigned_to_nat(32u);
v___x_1439_ = lean_mk_empty_array_with_capacity(v___x_1438_);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1441_ = ((size_t)5ULL);
v___x_1442_ = lean_unsigned_to_nat(0u);
v___x_1443_ = lean_unsigned_to_nat(32u);
v___x_1444_ = lean_mk_empty_array_with_capacity(v___x_1443_);
v___x_1445_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1446_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___x_1444_);
lean_ctor_set(v___x_1446_, 2, v___x_1442_);
lean_ctor_set(v___x_1446_, 3, v___x_1442_);
lean_ctor_set_usize(v___x_1446_, 4, v___x_1441_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_traceState_1450_; lean_object* v_traces_1451_; lean_object* v___x_1452_; lean_object* v_traceState_1453_; lean_object* v_env_1454_; lean_object* v_nextMacroScope_1455_; lean_object* v_ngen_1456_; lean_object* v_auxDeclNGen_1457_; lean_object* v_cache_1458_; lean_object* v_recordedDeps_1459_; lean_object* v_messages_1460_; lean_object* v_infoState_1461_; lean_object* v_snapshotTasks_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1481_; 
v___x_1449_ = lean_st_ref_get(v___y_1447_);
v_traceState_1450_ = lean_ctor_get(v___x_1449_, 4);
lean_inc_ref(v_traceState_1450_);
lean_dec(v___x_1449_);
v_traces_1451_ = lean_ctor_get(v_traceState_1450_, 0);
lean_inc_ref(v_traces_1451_);
lean_dec_ref(v_traceState_1450_);
v___x_1452_ = lean_st_ref_take(v___y_1447_);
v_traceState_1453_ = lean_ctor_get(v___x_1452_, 4);
v_env_1454_ = lean_ctor_get(v___x_1452_, 0);
v_nextMacroScope_1455_ = lean_ctor_get(v___x_1452_, 1);
v_ngen_1456_ = lean_ctor_get(v___x_1452_, 2);
v_auxDeclNGen_1457_ = lean_ctor_get(v___x_1452_, 3);
v_cache_1458_ = lean_ctor_get(v___x_1452_, 5);
v_recordedDeps_1459_ = lean_ctor_get(v___x_1452_, 6);
v_messages_1460_ = lean_ctor_get(v___x_1452_, 7);
v_infoState_1461_ = lean_ctor_get(v___x_1452_, 8);
v_snapshotTasks_1462_ = lean_ctor_get(v___x_1452_, 9);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1464_ = v___x_1452_;
v_isShared_1465_ = v_isSharedCheck_1481_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_snapshotTasks_1462_);
lean_inc(v_infoState_1461_);
lean_inc(v_messages_1460_);
lean_inc(v_recordedDeps_1459_);
lean_inc(v_cache_1458_);
lean_inc(v_traceState_1453_);
lean_inc(v_auxDeclNGen_1457_);
lean_inc(v_ngen_1456_);
lean_inc(v_nextMacroScope_1455_);
lean_inc(v_env_1454_);
lean_dec(v___x_1452_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1481_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
uint64_t v_tid_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1479_; 
v_tid_1466_ = lean_ctor_get_uint64(v_traceState_1453_, sizeof(void*)*1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_traceState_1453_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; 
v_unused_1480_ = lean_ctor_get(v_traceState_1453_, 0);
lean_dec(v_unused_1480_);
v___x_1468_ = v_traceState_1453_;
v_isShared_1469_ = v_isSharedCheck_1479_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v_traceState_1453_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1479_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1470_);
lean_ctor_set_uint64(v_reuseFailAlloc_1478_, sizeof(void*)*1, v_tid_1466_);
v___x_1472_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1474_; 
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 4, v___x_1472_);
v___x_1474_ = v___x_1464_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_env_1454_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_nextMacroScope_1455_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_ngen_1456_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_auxDeclNGen_1457_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1477_, 5, v_cache_1458_);
lean_ctor_set(v_reuseFailAlloc_1477_, 6, v_recordedDeps_1459_);
lean_ctor_set(v_reuseFailAlloc_1477_, 7, v_messages_1460_);
lean_ctor_set(v_reuseFailAlloc_1477_, 8, v_infoState_1461_);
lean_ctor_set(v_reuseFailAlloc_1477_, 9, v_snapshotTasks_1462_);
v___x_1474_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_st_ref_put(v___y_1447_, v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v_traces_1451_);
return v___x_1476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1482_);
lean_dec(v___y_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1497_, lean_object* v_opt_1498_){
_start:
{
lean_object* v_name_1499_; lean_object* v_defValue_1500_; lean_object* v_map_1501_; lean_object* v___x_1502_; 
v_name_1499_ = lean_ctor_get(v_opt_1498_, 0);
v_defValue_1500_ = lean_ctor_get(v_opt_1498_, 1);
v_map_1501_ = lean_ctor_get(v_opts_1497_, 0);
v___x_1502_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1501_, v_name_1499_);
if (lean_obj_tag(v___x_1502_) == 0)
{
uint8_t v___x_1503_; 
v___x_1503_ = lean_unbox(v_defValue_1500_);
return v___x_1503_;
}
else
{
lean_object* v_val_1504_; 
v_val_1504_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___x_1502_, 1);
if (lean_obj_tag(v_val_1504_) == 1)
{
uint8_t v_v_1505_; 
v_v_1505_ = lean_ctor_get_uint8(v_val_1504_, 0);
lean_dec_ref_known(v_val_1504_, 0);
return v_v_1505_;
}
else
{
uint8_t v___x_1506_; 
lean_dec(v_val_1504_);
v___x_1506_ = lean_unbox(v_defValue_1500_);
return v___x_1506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1507_, lean_object* v_opt_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1507_, v_opt_1508_);
lean_dec_ref(v_opt_1508_);
lean_dec_ref(v_opts_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1511_, lean_object* v_fnIndex_1512_, lean_object* v_recArg_1513_, lean_object* v_below_1514_, lean_object* v_Cs_1515_, lean_object* v_belowDict_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_array_get_borrowed(v___x_1511_, v_Cs_1515_, v_fnIndex_1512_);
lean_inc(v___x_1522_);
v___x_1523_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1522_, v_belowDict_1516_, v_recArg_1513_, v_below_1514_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1524_, lean_object* v_fnIndex_1525_, lean_object* v_recArg_1526_, lean_object* v_below_1527_, lean_object* v_Cs_1528_, lean_object* v_belowDict_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1524_, v_fnIndex_1525_, v_recArg_1526_, v_below_1527_, v_Cs_1528_, v_belowDict_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec_ref(v_Cs_1528_);
lean_dec(v_fnIndex_1525_);
lean_dec_ref(v___x_1524_);
return v_res_1535_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1538_ = l_Lean_stringToMessageData(v___x_1537_);
return v___x_1538_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1541_ = l_Lean_stringToMessageData(v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1542_, lean_object* v_recArg_1543_, lean_object* v_x_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
lean_inc(v___y_1548_);
lean_inc_ref(v___y_1547_);
lean_inc(v___y_1546_);
lean_inc_ref(v___y_1545_);
v___x_1550_ = lean_infer_type(v_below_1542_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1565_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1565_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1565_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1555_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1556_ = l_Lean_MessageData_ofExpr(v_recArg_1543_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_MessageData_ofExpr(v_a_1551_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v___x_1561_);
v___x_1563_ = v___x_1553_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v_recArg_1543_);
v_a_1566_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1550_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1550_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1574_, lean_object* v_recArg_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1574_, v_recArg_1575_, v_x_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
lean_dec(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec(v___y_1578_);
lean_dec_ref(v___y_1577_);
lean_dec_ref(v_x_1576_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1583_, size_t v_i_1584_, lean_object* v_bs_1585_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = lean_usize_dec_lt(v_i_1584_, v_sz_1583_);
if (v___x_1586_ == 0)
{
return v_bs_1585_;
}
else
{
lean_object* v_v_1587_; lean_object* v_msg_1588_; lean_object* v___x_1589_; lean_object* v_bs_x27_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; 
v_v_1587_ = lean_array_uget_borrowed(v_bs_1585_, v_i_1584_);
v_msg_1588_ = lean_ctor_get(v_v_1587_, 1);
lean_inc_ref(v_msg_1588_);
v___x_1589_ = lean_unsigned_to_nat(0u);
v_bs_x27_1590_ = lean_array_uset(v_bs_1585_, v_i_1584_, v___x_1589_);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_i_1584_, v___x_1591_);
v___x_1593_ = lean_array_uset(v_bs_x27_1590_, v_i_1584_, v_msg_1588_);
v_i_1584_ = v___x_1592_;
v_bs_1585_ = v___x_1593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1595_, lean_object* v_i_1596_, lean_object* v_bs_1597_){
_start:
{
size_t v_sz_boxed_1598_; size_t v_i_boxed_1599_; lean_object* v_res_1600_; 
v_sz_boxed_1598_ = lean_unbox_usize(v_sz_1595_);
lean_dec(v_sz_1595_);
v_i_boxed_1599_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_res_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_boxed_1598_, v_i_boxed_1599_, v_bs_1597_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1601_, lean_object* v_data_1602_, lean_object* v_ref_1603_, lean_object* v_msg_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_toCold_1610_; lean_object* v_currRecDepth_1611_; lean_object* v_ref_1612_; uint16_t v_optionFlags_1613_; uint8_t v_suppressElabErrors_1614_; uint8_t v_isRecordingDeps_1615_; lean_object* v_ref_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_traceState_1619_; lean_object* v_traces_1620_; lean_object* v___x_1621_; size_t v_sz_1622_; size_t v___x_1623_; lean_object* v___x_1624_; lean_object* v_msg_1625_; lean_object* v___x_1626_; lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1665_; 
v_toCold_1610_ = lean_ctor_get(v___y_1607_, 0);
v_currRecDepth_1611_ = lean_ctor_get(v___y_1607_, 1);
v_ref_1612_ = lean_ctor_get(v___y_1607_, 2);
v_optionFlags_1613_ = lean_ctor_get_uint16(v___y_1607_, sizeof(void*)*3);
v_suppressElabErrors_1614_ = lean_ctor_get_uint8(v___y_1607_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1615_ = lean_ctor_get_uint8(v___y_1607_, sizeof(void*)*3 + 3);
v_ref_1616_ = l_Lean_replaceRef(v_ref_1603_, v_ref_1612_);
lean_inc(v_currRecDepth_1611_);
lean_inc_ref(v_toCold_1610_);
v___x_1617_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1617_, 0, v_toCold_1610_);
lean_ctor_set(v___x_1617_, 1, v_currRecDepth_1611_);
lean_ctor_set(v___x_1617_, 2, v_ref_1616_);
lean_ctor_set_uint16(v___x_1617_, sizeof(void*)*3, v_optionFlags_1613_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*3 + 2, v_suppressElabErrors_1614_);
lean_ctor_set_uint8(v___x_1617_, sizeof(void*)*3 + 3, v_isRecordingDeps_1615_);
v___x_1618_ = lean_st_ref_get(v___y_1608_);
v_traceState_1619_ = lean_ctor_get(v___x_1618_, 4);
lean_inc_ref(v_traceState_1619_);
lean_dec(v___x_1618_);
v_traces_1620_ = lean_ctor_get(v_traceState_1619_, 0);
lean_inc_ref(v_traces_1620_);
lean_dec_ref(v_traceState_1619_);
v___x_1621_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1620_);
lean_dec_ref(v_traces_1620_);
v_sz_1622_ = lean_array_size(v___x_1621_);
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1622_, v___x_1623_, v___x_1621_);
v_msg_1625_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1625_, 0, v_data_1602_);
lean_ctor_set(v_msg_1625_, 1, v_msg_1604_);
lean_ctor_set(v_msg_1625_, 2, v___x_1624_);
v___x_1626_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1625_, v___y_1605_, v___y_1606_, v___x_1617_, v___y_1608_);
lean_dec_ref_known(v___x_1617_, 3);
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1665_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1665_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v_traceState_1632_; lean_object* v_env_1633_; lean_object* v_nextMacroScope_1634_; lean_object* v_ngen_1635_; lean_object* v_auxDeclNGen_1636_; lean_object* v_cache_1637_; lean_object* v_recordedDeps_1638_; lean_object* v_messages_1639_; lean_object* v_infoState_1640_; lean_object* v_snapshotTasks_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1664_; 
v___x_1631_ = lean_st_ref_take(v___y_1608_);
v_traceState_1632_ = lean_ctor_get(v___x_1631_, 4);
v_env_1633_ = lean_ctor_get(v___x_1631_, 0);
v_nextMacroScope_1634_ = lean_ctor_get(v___x_1631_, 1);
v_ngen_1635_ = lean_ctor_get(v___x_1631_, 2);
v_auxDeclNGen_1636_ = lean_ctor_get(v___x_1631_, 3);
v_cache_1637_ = lean_ctor_get(v___x_1631_, 5);
v_recordedDeps_1638_ = lean_ctor_get(v___x_1631_, 6);
v_messages_1639_ = lean_ctor_get(v___x_1631_, 7);
v_infoState_1640_ = lean_ctor_get(v___x_1631_, 8);
v_snapshotTasks_1641_ = lean_ctor_get(v___x_1631_, 9);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1643_ = v___x_1631_;
v_isShared_1644_ = v_isSharedCheck_1664_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_snapshotTasks_1641_);
lean_inc(v_infoState_1640_);
lean_inc(v_messages_1639_);
lean_inc(v_recordedDeps_1638_);
lean_inc(v_cache_1637_);
lean_inc(v_traceState_1632_);
lean_inc(v_auxDeclNGen_1636_);
lean_inc(v_ngen_1635_);
lean_inc(v_nextMacroScope_1634_);
lean_inc(v_env_1633_);
lean_dec(v___x_1631_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1664_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
uint64_t v_tid_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1662_; 
v_tid_1645_ = lean_ctor_get_uint64(v_traceState_1632_, sizeof(void*)*1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_traceState_1632_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v_traceState_1632_, 0);
lean_dec(v_unused_1663_);
v___x_1647_ = v_traceState_1632_;
v_isShared_1648_ = v_isSharedCheck_1662_;
goto v_resetjp_1646_;
}
else
{
lean_dec(v_traceState_1632_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1662_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1650_, 0, v_ref_1603_);
lean_ctor_set(v___x_1650_, 1, v_a_1627_);
v___x_1651_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1601_, v___x_1650_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1651_);
v___x_1653_ = v___x_1647_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1651_);
lean_ctor_set_uint64(v_reuseFailAlloc_1661_, sizeof(void*)*1, v_tid_1645_);
v___x_1653_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v___x_1653_);
v___x_1655_ = v___x_1643_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_env_1633_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_nextMacroScope_1634_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_ngen_1635_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_auxDeclNGen_1636_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1660_, 5, v_cache_1637_);
lean_ctor_set(v_reuseFailAlloc_1660_, 6, v_recordedDeps_1638_);
lean_ctor_set(v_reuseFailAlloc_1660_, 7, v_messages_1639_);
lean_ctor_set(v_reuseFailAlloc_1660_, 8, v_infoState_1640_);
lean_ctor_set(v_reuseFailAlloc_1660_, 9, v_snapshotTasks_1641_);
v___x_1655_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1658_; 
v___x_1656_ = lean_st_ref_put(v___y_1608_, v___x_1655_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1649_);
v___x_1658_ = v___x_1629_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1649_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1666_, lean_object* v_data_1667_, lean_object* v_ref_1668_, lean_object* v_msg_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1666_, v_data_1667_, v_ref_1668_, v_msg_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1676_, lean_object* v_opt_1677_){
_start:
{
lean_object* v_name_1678_; lean_object* v_defValue_1679_; lean_object* v_map_1680_; lean_object* v___x_1681_; 
v_name_1678_ = lean_ctor_get(v_opt_1677_, 0);
v_defValue_1679_ = lean_ctor_get(v_opt_1677_, 1);
v_map_1680_ = lean_ctor_get(v_opts_1676_, 0);
v___x_1681_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1680_, v_name_1678_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_inc(v_defValue_1679_);
return v_defValue_1679_;
}
else
{
lean_object* v_val_1682_; 
v_val_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref_known(v___x_1681_, 1);
if (lean_obj_tag(v_val_1682_) == 3)
{
lean_object* v_v_1683_; 
v_v_1683_ = lean_ctor_get(v_val_1682_, 0);
lean_inc(v_v_1683_);
lean_dec_ref_known(v_val_1682_, 1);
return v_v_1683_;
}
else
{
lean_dec(v_val_1682_);
lean_inc(v_defValue_1679_);
return v_defValue_1679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1684_, lean_object* v_opt_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1684_, v_opt_1685_);
lean_dec_ref(v_opt_1685_);
lean_dec_ref(v_opts_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1687_){
_start:
{
if (lean_obj_tag(v_e_1687_) == 0)
{
uint8_t v___x_1688_; 
v___x_1688_ = 2;
return v___x_1688_;
}
else
{
lean_object* v_a_1689_; uint8_t v___x_1690_; 
v_a_1689_ = lean_ctor_get(v_e_1687_, 0);
v___x_1690_ = l_Lean_Expr_hasSyntheticSorry(v_a_1689_);
if (v___x_1690_ == 0)
{
uint8_t v___x_1691_; 
v___x_1691_ = 0;
return v___x_1691_;
}
else
{
uint8_t v___x_1692_; 
v___x_1692_ = 1;
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1693_){
_start:
{
uint8_t v_res_1694_; lean_object* v_r_1695_; 
v_res_1694_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1693_);
lean_dec_ref(v_e_1693_);
v_r_1695_ = lean_box(v_res_1694_);
return v_r_1695_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1696_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v_x_1696_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v_x_1696_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v_x_1696_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 1);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_a_1706_ = lean_ctor_get(v_x_1696_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_x_1696_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v_x_1696_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v_x_1696_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
lean_ctor_set_tag(v___x_1708_, 0);
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1714_);
return v_res_1716_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1719_ = l_Lean_stringToMessageData(v___x_1718_);
return v___x_1719_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1720_; double v___x_1721_; 
v___x_1720_ = lean_unsigned_to_nat(1000u);
v___x_1721_ = lean_float_of_nat(v___x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1722_, uint8_t v_collapsed_1723_, lean_object* v_tag_1724_, lean_object* v_opts_1725_, uint8_t v_clsEnabled_1726_, lean_object* v_oldTraces_1727_, lean_object* v_msg_1728_, lean_object* v_resStartStop_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_fst_1735_; lean_object* v_snd_1736_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v_data_1740_; lean_object* v_fst_1751_; lean_object* v_snd_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; lean_object* v___y_1756_; lean_object* v_a_1757_; uint8_t v___y_1772_; double v___y_1804_; 
v_fst_1735_ = lean_ctor_get(v_resStartStop_1729_, 0);
lean_inc(v_fst_1735_);
v_snd_1736_ = lean_ctor_get(v_resStartStop_1729_, 1);
lean_inc(v_snd_1736_);
lean_dec_ref(v_resStartStop_1729_);
v_fst_1751_ = lean_ctor_get(v_snd_1736_, 0);
lean_inc(v_fst_1751_);
v_snd_1752_ = lean_ctor_get(v_snd_1736_, 1);
lean_inc(v_snd_1752_);
lean_dec(v_snd_1736_);
v___x_1753_ = l_Lean_trace_profiler;
v___x_1754_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1725_, v___x_1753_);
if (v___x_1754_ == 0)
{
v___y_1772_ = v___x_1754_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1810_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1725_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; double v___x_1813_; double v___x_1814_; double v___x_1815_; 
v___x_1811_ = l_Lean_trace_profiler_threshold;
v___x_1812_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1725_, v___x_1811_);
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
v___x_1817_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1725_, v___x_1816_);
v___x_1818_ = lean_float_of_nat(v___x_1817_);
v___y_1804_ = v___x_1818_;
goto v___jp_1803_;
}
}
v___jp_1737_:
{
lean_object* v___x_1741_; 
lean_inc(v___y_1738_);
v___x_1741_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1727_, v_data_1740_, v___y_1738_, v___y_1739_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref_known(v___x_1741_, 1);
v___x_1742_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1735_);
return v___x_1742_;
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v_fst_1735_);
v_a_1743_ = lean_ctor_get(v___x_1741_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1741_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1741_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
v___jp_1755_:
{
uint8_t v_result_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; double v___x_1761_; lean_object* v_data_1762_; 
v_result_1758_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1735_);
v___x_1759_ = lean_box(v_result_1758_);
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1759_);
v___x_1761_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1724_);
lean_inc_ref(v___x_1760_);
lean_inc(v_cls_1722_);
v_data_1762_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1762_, 0, v_cls_1722_);
lean_ctor_set(v_data_1762_, 1, v___x_1760_);
lean_ctor_set(v_data_1762_, 2, v_tag_1724_);
lean_ctor_set_float(v_data_1762_, sizeof(void*)*3, v___x_1761_);
lean_ctor_set_float(v_data_1762_, sizeof(void*)*3 + 8, v___x_1761_);
lean_ctor_set_uint8(v_data_1762_, sizeof(void*)*3 + 16, v_collapsed_1723_);
if (v___x_1754_ == 0)
{
lean_dec_ref_known(v___x_1760_, 1);
lean_dec(v_snd_1752_);
lean_dec(v_fst_1751_);
lean_dec_ref(v_tag_1724_);
lean_dec(v_cls_1722_);
v___y_1738_ = v___y_1756_;
v___y_1739_ = v_a_1757_;
v_data_1740_ = v_data_1762_;
goto v___jp_1737_;
}
else
{
lean_object* v_data_1763_; double v___x_1764_; double v___x_1765_; 
lean_dec_ref_known(v_data_1762_, 3);
v_data_1763_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1763_, 0, v_cls_1722_);
lean_ctor_set(v_data_1763_, 1, v___x_1760_);
lean_ctor_set(v_data_1763_, 2, v_tag_1724_);
v___x_1764_ = lean_unbox_float(v_fst_1751_);
lean_dec(v_fst_1751_);
lean_ctor_set_float(v_data_1763_, sizeof(void*)*3, v___x_1764_);
v___x_1765_ = lean_unbox_float(v_snd_1752_);
lean_dec(v_snd_1752_);
lean_ctor_set_float(v_data_1763_, sizeof(void*)*3 + 8, v___x_1765_);
lean_ctor_set_uint8(v_data_1763_, sizeof(void*)*3 + 16, v_collapsed_1723_);
v___y_1738_ = v___y_1756_;
v___y_1739_ = v_a_1757_;
v_data_1740_ = v_data_1763_;
goto v___jp_1737_;
}
}
v___jp_1766_:
{
lean_object* v_ref_1767_; lean_object* v___x_1768_; 
v_ref_1767_ = lean_ctor_get(v___y_1732_, 2);
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
lean_inc(v_fst_1735_);
v___x_1768_ = lean_apply_6(v_msg_1728_, v_fst_1735_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, lean_box(0));
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v___y_1756_ = v_ref_1767_;
v_a_1757_ = v_a_1769_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1768_, 1);
v___x_1770_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1756_ = v_ref_1767_;
v_a_1757_ = v___x_1770_;
goto v___jp_1755_;
}
}
v___jp_1771_:
{
if (v_clsEnabled_1726_ == 0)
{
if (v___y_1772_ == 0)
{
lean_object* v___x_1773_; lean_object* v_traceState_1774_; lean_object* v_env_1775_; lean_object* v_nextMacroScope_1776_; lean_object* v_ngen_1777_; lean_object* v_auxDeclNGen_1778_; lean_object* v_cache_1779_; lean_object* v_recordedDeps_1780_; lean_object* v_messages_1781_; lean_object* v_infoState_1782_; lean_object* v_snapshotTasks_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_snd_1752_);
lean_dec(v_fst_1751_);
lean_dec_ref(v_msg_1728_);
lean_dec_ref(v_tag_1724_);
lean_dec(v_cls_1722_);
v___x_1773_ = lean_st_ref_take(v___y_1733_);
v_traceState_1774_ = lean_ctor_get(v___x_1773_, 4);
v_env_1775_ = lean_ctor_get(v___x_1773_, 0);
v_nextMacroScope_1776_ = lean_ctor_get(v___x_1773_, 1);
v_ngen_1777_ = lean_ctor_get(v___x_1773_, 2);
v_auxDeclNGen_1778_ = lean_ctor_get(v___x_1773_, 3);
v_cache_1779_ = lean_ctor_get(v___x_1773_, 5);
v_recordedDeps_1780_ = lean_ctor_get(v___x_1773_, 6);
v_messages_1781_ = lean_ctor_get(v___x_1773_, 7);
v_infoState_1782_ = lean_ctor_get(v___x_1773_, 8);
v_snapshotTasks_1783_ = lean_ctor_get(v___x_1773_, 9);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1785_ = v___x_1773_;
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_snapshotTasks_1783_);
lean_inc(v_infoState_1782_);
lean_inc(v_messages_1781_);
lean_inc(v_recordedDeps_1780_);
lean_inc(v_cache_1779_);
lean_inc(v_traceState_1774_);
lean_inc(v_auxDeclNGen_1778_);
lean_inc(v_ngen_1777_);
lean_inc(v_nextMacroScope_1776_);
lean_inc(v_env_1775_);
lean_dec(v___x_1773_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1802_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
uint64_t v_tid_1787_; lean_object* v_traces_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1801_; 
v_tid_1787_ = lean_ctor_get_uint64(v_traceState_1774_, sizeof(void*)*1);
v_traces_1788_ = lean_ctor_get(v_traceState_1774_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_traceState_1774_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1790_ = v_traceState_1774_;
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_traces_1788_);
lean_dec(v_traceState_1774_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1727_, v_traces_1788_);
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
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_env_1775_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_nextMacroScope_1776_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_ngen_1777_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_auxDeclNGen_1778_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_cache_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_recordedDeps_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_messages_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_infoState_1782_);
lean_ctor_set(v_reuseFailAlloc_1799_, 9, v_snapshotTasks_1783_);
v___x_1796_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = lean_st_ref_put(v___y_1733_, v___x_1796_);
v___x_1798_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1735_);
return v___x_1798_;
}
}
}
}
}
else
{
goto v___jp_1766_;
}
}
else
{
goto v___jp_1766_;
}
}
v___jp_1803_:
{
double v___x_1805_; double v___x_1806_; double v___x_1807_; uint8_t v___x_1808_; 
v___x_1805_ = lean_unbox_float(v_snd_1752_);
v___x_1806_ = lean_unbox_float(v_fst_1751_);
v___x_1807_ = lean_float_sub(v___x_1805_, v___x_1806_);
v___x_1808_ = lean_float_decLt(v___y_1804_, v___x_1807_);
v___y_1772_ = v___x_1808_;
goto v___jp_1771_;
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
static double _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1835_; double v___x_1836_; 
v___x_1835_ = lean_unsigned_to_nat(1000000000u);
v___x_1836_ = lean_float_of_nat(v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1837_, lean_object* v_numIndParams_1838_, lean_object* v_positions_1839_, lean_object* v_fnIndex_1840_, lean_object* v_recArg_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_toCold_1847_; lean_object* v_options_1848_; lean_object* v_inheritedTraceOptions_1849_; uint8_t v_hasTrace_1850_; lean_object* v___x_1851_; lean_object* v___f_1852_; 
v_toCold_1847_ = lean_ctor_get(v_a_1844_, 0);
v_options_1848_ = lean_ctor_get(v_toCold_1847_, 2);
v_inheritedTraceOptions_1849_ = lean_ctor_get(v_toCold_1847_, 11);
v_hasTrace_1850_ = lean_ctor_get_uint8(v_options_1848_, sizeof(void*)*1);
v___x_1851_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1837_);
lean_inc_ref(v_recArg_1841_);
v___f_1852_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1852_, 0, v___x_1851_);
lean_closure_set(v___f_1852_, 1, v_fnIndex_1840_);
lean_closure_set(v___f_1852_, 2, v_recArg_1841_);
lean_closure_set(v___f_1852_, 3, v_below_1837_);
if (v_hasTrace_1850_ == 0)
{
lean_object* v___x_1853_; 
lean_dec_ref(v_recArg_1841_);
v___x_1853_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1837_, v_numIndParams_1838_, v_positions_1839_, v___f_1852_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1853_;
}
else
{
lean_object* v___f_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v_a_1862_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v_a_1877_; 
lean_inc_ref(v_below_1837_);
v___f_1854_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1854_, 0, v_below_1837_);
lean_closure_set(v___f_1854_, 1, v_recArg_1841_);
v___x_1855_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1856_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1857_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1858_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1849_, v_options_1848_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = l_Lean_trace_profiler;
v___x_1928_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1848_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1929_; 
lean_dec_ref(v___f_1854_);
v___x_1929_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1837_, v_numIndParams_1838_, v_positions_1839_, v___f_1852_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1929_;
}
else
{
goto v___jp_1886_;
}
}
else
{
goto v___jp_1886_;
}
v___jp_1859_:
{
lean_object* v___x_1863_; double v___x_1864_; double v___x_1865_; double v___x_1866_; double v___x_1867_; double v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1863_ = lean_io_mono_nanos_now();
v___x_1864_ = lean_float_of_nat(v___y_1861_);
v___x_1865_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1866_ = lean_float_div(v___x_1864_, v___x_1865_);
v___x_1867_ = lean_float_of_nat(v___x_1863_);
v___x_1868_ = lean_float_div(v___x_1867_, v___x_1865_);
v___x_1869_ = lean_box_float(v___x_1866_);
v___x_1870_ = lean_box_float(v___x_1868_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1862_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1855_, v_hasTrace_1850_, v___x_1856_, v_options_1848_, v___x_1858_, v___y_1860_, v___f_1854_, v___x_1872_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1873_;
}
v___jp_1874_:
{
lean_object* v___x_1878_; double v___x_1879_; double v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1878_ = lean_io_get_num_heartbeats();
v___x_1879_ = lean_float_of_nat(v___y_1876_);
v___x_1880_ = lean_float_of_nat(v___x_1878_);
v___x_1881_ = lean_box_float(v___x_1879_);
v___x_1882_ = lean_box_float(v___x_1880_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_a_1877_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1855_, v_hasTrace_1850_, v___x_1856_, v_options_1848_, v___x_1858_, v___y_1875_, v___f_1854_, v___x_1884_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
return v___x_1885_;
}
v___jp_1886_:
{
lean_object* v___x_1887_; lean_object* v_a_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1887_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1845_);
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1890_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1848_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_io_mono_nanos_now();
v___x_1892_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1837_, v_numIndParams_1838_, v_positions_1839_, v___f_1852_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 1);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v___y_1860_ = v_a_1888_;
v___y_1861_ = v___x_1891_;
v_a_1862_ = v___x_1898_;
goto v___jp_1859_;
}
}
}
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
v_a_1901_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1892_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1892_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 0);
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
v___y_1860_ = v_a_1888_;
v___y_1861_ = v___x_1891_;
v_a_1862_ = v___x_1906_;
goto v___jp_1859_;
}
}
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_io_get_num_heartbeats();
v___x_1910_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1837_, v_numIndParams_1838_, v_positions_1839_, v___f_1852_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 1);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
v___y_1875_ = v_a_1888_;
v___y_1876_ = v___x_1909_;
v_a_1877_ = v___x_1916_;
goto v___jp_1874_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_a_1919_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1910_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1910_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set_tag(v___x_1921_, 0);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
v___y_1875_ = v_a_1888_;
v___y_1876_ = v___x_1909_;
v_a_1877_ = v___x_1924_;
goto v___jp_1874_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1930_, lean_object* v_numIndParams_1931_, lean_object* v_positions_1932_, lean_object* v_fnIndex_1933_, lean_object* v_recArg_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_Elab_Structural_toBelow(v_below_1930_, v_numIndParams_1931_, v_positions_1932_, v_fnIndex_1933_, v_recArg_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1937_);
lean_dec(v_a_1936_);
lean_dec_ref(v_a_1935_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1941_, lean_object* v_x_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1942_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1949_, lean_object* v_x_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1949_, v_x_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1957_, lean_object* v___y_1958_, lean_object* v_b_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
lean_inc(v___y_1963_);
lean_inc_ref(v___y_1962_);
lean_inc(v___y_1961_);
lean_inc_ref(v___y_1960_);
lean_inc(v___y_1958_);
v___x_1965_ = lean_apply_7(v_k_1957_, v_b_1959_, v___y_1958_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, lean_box(0));
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_1966_, lean_object* v___y_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1966_, v___y_1967_, v_b_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1967_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_1975_, uint8_t v_bi_1976_, lean_object* v_type_1977_, lean_object* v_k_1978_, uint8_t v_kind_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___f_1986_; lean_object* v___x_1987_; 
lean_inc(v___y_1980_);
v___f_1986_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1986_, 0, v_k_1978_);
lean_closure_set(v___f_1986_, 1, v___y_1980_);
v___x_1987_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1975_, v_bi_1976_, v_type_1977_, v___f_1986_, v_kind_1979_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_1987_) == 0)
{
return v___x_1987_;
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_1996_, lean_object* v_bi_1997_, lean_object* v_type_1998_, lean_object* v_k_1999_, lean_object* v_kind_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v_bi_boxed_2007_; uint8_t v_kind_boxed_2008_; lean_object* v_res_2009_; 
v_bi_boxed_2007_ = lean_unbox(v_bi_1997_);
v_kind_boxed_2008_ = lean_unbox(v_kind_2000_);
v_res_2009_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_1996_, v_bi_boxed_2007_, v_type_1998_, v_k_1999_, v_kind_boxed_2008_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2010_, lean_object* v_name_2011_, uint8_t v_bi_2012_, lean_object* v_type_2013_, lean_object* v_k_2014_, uint8_t v_kind_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2011_, v_bi_2012_, v_type_2013_, v_k_2014_, v_kind_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_name_2024_, lean_object* v_bi_2025_, lean_object* v_type_2026_, lean_object* v_k_2027_, lean_object* v_kind_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
uint8_t v_bi_boxed_2035_; uint8_t v_kind_boxed_2036_; lean_object* v_res_2037_; 
v_bi_boxed_2035_ = lean_unbox(v_bi_2025_);
v_kind_boxed_2036_ = lean_unbox(v_kind_2028_);
v_res_2037_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2023_, v_name_2024_, v_bi_boxed_2035_, v_type_2026_, v_k_2027_, v_kind_boxed_2036_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2038_, lean_object* v___y_2039_, lean_object* v_b_2040_, lean_object* v_c_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
lean_inc(v___y_2045_);
lean_inc_ref(v___y_2044_);
lean_inc(v___y_2043_);
lean_inc_ref(v___y_2042_);
lean_inc(v___y_2039_);
v___x_2047_ = lean_apply_8(v_k_2038_, v_b_2040_, v_c_2041_, v___y_2039_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, lean_box(0));
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed(lean_object* v_k_2048_, lean_object* v___y_2049_, lean_object* v_b_2050_, lean_object* v_c_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2048_, v___y_2049_, v_b_2050_, v_c_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2049_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2058_, lean_object* v_maxFVars_2059_, lean_object* v_k_2060_, uint8_t v_cleanupAnnotations_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___f_2068_; uint8_t v___x_2069_; uint8_t v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
lean_inc(v___y_2062_);
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2068_, 0, v_k_2060_);
lean_closure_set(v___f_2068_, 1, v___y_2062_);
v___x_2069_ = 1;
v___x_2070_ = 0;
v___x_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_maxFVars_2059_);
v___x_2072_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2058_, v___x_2069_, v___x_2070_, v___x_2069_, v___x_2070_, v___x_2071_, v___f_2068_, v_cleanupAnnotations_2061_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec_ref_known(v___x_2071_, 1);
if (lean_obj_tag(v___x_2072_) == 0)
{
return v___x_2072_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2072_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2072_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2081_, lean_object* v_maxFVars_2082_, lean_object* v_k_2083_, lean_object* v_cleanupAnnotations_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2091_; lean_object* v_res_2092_; 
v_cleanupAnnotations_boxed_2091_ = lean_unbox(v_cleanupAnnotations_2084_);
v_res_2092_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2081_, v_maxFVars_2082_, v_k_2083_, v_cleanupAnnotations_boxed_2091_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_);
lean_dec(v___y_2089_);
lean_dec_ref(v___y_2088_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2093_, lean_object* v_e_2094_, lean_object* v_maxFVars_2095_, lean_object* v_k_2096_, uint8_t v_cleanupAnnotations_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2094_, v_maxFVars_2095_, v_k_2096_, v_cleanupAnnotations_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2105_, lean_object* v_e_2106_, lean_object* v_maxFVars_2107_, lean_object* v_k_2108_, lean_object* v_cleanupAnnotations_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2116_; lean_object* v_res_2117_; 
v_cleanupAnnotations_boxed_2116_ = lean_unbox(v_cleanupAnnotations_2109_);
v_res_2117_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2105_, v_e_2106_, v_maxFVars_2107_, v_k_2108_, v_cleanupAnnotations_boxed_2116_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2118_, lean_object* v_msg_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_ref_2125_; lean_object* v___x_2126_; lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2172_; 
v_ref_2125_ = lean_ctor_get(v___y_2122_, 2);
v___x_2126_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2172_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2172_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v_traceState_2132_; lean_object* v_env_2133_; lean_object* v_nextMacroScope_2134_; lean_object* v_ngen_2135_; lean_object* v_auxDeclNGen_2136_; lean_object* v_cache_2137_; lean_object* v_recordedDeps_2138_; lean_object* v_messages_2139_; lean_object* v_infoState_2140_; lean_object* v_snapshotTasks_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2171_; 
v___x_2131_ = lean_st_ref_take(v___y_2123_);
v_traceState_2132_ = lean_ctor_get(v___x_2131_, 4);
v_env_2133_ = lean_ctor_get(v___x_2131_, 0);
v_nextMacroScope_2134_ = lean_ctor_get(v___x_2131_, 1);
v_ngen_2135_ = lean_ctor_get(v___x_2131_, 2);
v_auxDeclNGen_2136_ = lean_ctor_get(v___x_2131_, 3);
v_cache_2137_ = lean_ctor_get(v___x_2131_, 5);
v_recordedDeps_2138_ = lean_ctor_get(v___x_2131_, 6);
v_messages_2139_ = lean_ctor_get(v___x_2131_, 7);
v_infoState_2140_ = lean_ctor_get(v___x_2131_, 8);
v_snapshotTasks_2141_ = lean_ctor_get(v___x_2131_, 9);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2143_ = v___x_2131_;
v_isShared_2144_ = v_isSharedCheck_2171_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_snapshotTasks_2141_);
lean_inc(v_infoState_2140_);
lean_inc(v_messages_2139_);
lean_inc(v_recordedDeps_2138_);
lean_inc(v_cache_2137_);
lean_inc(v_traceState_2132_);
lean_inc(v_auxDeclNGen_2136_);
lean_inc(v_ngen_2135_);
lean_inc(v_nextMacroScope_2134_);
lean_inc(v_env_2133_);
lean_dec(v___x_2131_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2171_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
uint64_t v_tid_2145_; lean_object* v_traces_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2170_; 
v_tid_2145_ = lean_ctor_get_uint64(v_traceState_2132_, sizeof(void*)*1);
v_traces_2146_ = lean_ctor_get(v_traceState_2132_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_traceState_2132_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2148_ = v_traceState_2132_;
v_isShared_2149_ = v_isSharedCheck_2170_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_traces_2146_);
lean_dec(v_traceState_2132_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2170_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; double v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_box(0);
v___x_2152_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2153_ = 0;
v___x_2154_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2155_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2155_, 0, v_cls_2118_);
lean_ctor_set(v___x_2155_, 1, v___x_2151_);
lean_ctor_set(v___x_2155_, 2, v___x_2154_);
lean_ctor_set_float(v___x_2155_, sizeof(void*)*3, v___x_2152_);
lean_ctor_set_float(v___x_2155_, sizeof(void*)*3 + 8, v___x_2152_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*3 + 16, v___x_2153_);
v___x_2156_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2157_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v_a_2127_);
lean_ctor_set(v___x_2157_, 2, v___x_2156_);
lean_inc(v_ref_2125_);
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v_ref_2125_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_PersistentArray_push___redArg(v_traces_2146_, v___x_2158_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2159_);
v___x_2161_ = v___x_2148_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2159_);
lean_ctor_set_uint64(v_reuseFailAlloc_2169_, sizeof(void*)*1, v_tid_2145_);
v___x_2161_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
lean_object* v___x_2163_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 4, v___x_2161_);
v___x_2163_ = v___x_2143_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_env_2133_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_nextMacroScope_2134_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v_ngen_2135_);
lean_ctor_set(v_reuseFailAlloc_2168_, 3, v_auxDeclNGen_2136_);
lean_ctor_set(v_reuseFailAlloc_2168_, 4, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2168_, 5, v_cache_2137_);
lean_ctor_set(v_reuseFailAlloc_2168_, 6, v_recordedDeps_2138_);
lean_ctor_set(v_reuseFailAlloc_2168_, 7, v_messages_2139_);
lean_ctor_set(v_reuseFailAlloc_2168_, 8, v_infoState_2140_);
lean_ctor_set(v_reuseFailAlloc_2168_, 9, v_snapshotTasks_2141_);
v___x_2163_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_st_ref_put(v___y_2123_, v___x_2163_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2150_);
v___x_2166_ = v___x_2129_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2150_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2173_, lean_object* v_msg_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2173_, v_msg_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2181_, lean_object* v_as_2182_, size_t v_i_2183_, size_t v_stop_2184_){
_start:
{
uint8_t v___x_2189_; 
v___x_2189_ = lean_usize_dec_eq(v_i_2183_, v_stop_2184_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v_fnName_2191_; lean_object* v_recArgPos_2192_; uint8_t v___x_2193_; 
v___x_2190_ = lean_array_uget_borrowed(v_as_2182_, v_i_2183_);
v_fnName_2191_ = lean_ctor_get(v___x_2190_, 0);
v_recArgPos_2192_ = lean_ctor_get(v___x_2190_, 2);
lean_inc(v_recArgPos_2192_);
lean_inc(v_fnName_2191_);
v___x_2193_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2191_, v_recArgPos_2192_, v_e_2181_);
if (v___x_2193_ == 0)
{
goto v___jp_2185_;
}
else
{
if (v___x_2193_ == 0)
{
goto v___jp_2185_;
}
else
{
return v___x_2193_;
}
}
}
else
{
uint8_t v___x_2194_; 
v___x_2194_ = 0;
return v___x_2194_;
}
v___jp_2185_:
{
size_t v___x_2186_; size_t v___x_2187_; 
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2183_, v___x_2186_);
v_i_2183_ = v___x_2187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2195_, lean_object* v_as_2196_, lean_object* v_i_2197_, lean_object* v_stop_2198_){
_start:
{
size_t v_i_boxed_2199_; size_t v_stop_boxed_2200_; uint8_t v_res_2201_; lean_object* v_r_2202_; 
v_i_boxed_2199_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_stop_boxed_2200_ = lean_unbox_usize(v_stop_2198_);
lean_dec(v_stop_2198_);
v_res_2201_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2195_, v_as_2196_, v_i_boxed_2199_, v_stop_boxed_2200_);
lean_dec_ref(v_as_2196_);
lean_dec_ref(v_e_2195_);
v_r_2202_ = lean_box(v_res_2201_);
return v_r_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2203_, lean_object* v_____do__lift_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_toCold_2211_; lean_object* v_options_2212_; uint8_t v_hasTrace_2213_; 
v_toCold_2211_ = lean_ctor_get(v___y_2208_, 0);
v_options_2212_ = lean_ctor_get(v_toCold_2211_, 2);
v_hasTrace_2213_ = lean_ctor_get_uint8(v_options_2212_, sizeof(void*)*1);
if (v_hasTrace_2213_ == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
lean_dec(v___x_2203_);
v___x_2214_ = lean_box(v_hasTrace_2213_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2216_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2217_ = l_Lean_Name_append(v___x_2216_, v___x_2203_);
v___x_2218_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2204_, v_options_2212_, v___x_2217_);
lean_dec(v___x_2217_);
v___x_2219_ = lean_box(v___x_2218_);
v___x_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2221_, lean_object* v_____do__lift_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2221_, v_____do__lift_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v_____do__lift_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; lean_object* v_env_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2233_ = lean_st_ref_get(v___y_2231_);
v_env_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc_ref(v_env_2234_);
lean_dec(v___x_2233_);
v___x_2235_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2234_, v_declName_2230_);
v___x_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2237_, v___y_2238_);
lean_dec(v___y_2238_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_toApplicative_2249_; lean_object* v_toFunctor_2250_; lean_object* v_toSeq_2251_; lean_object* v_toSeqLeft_2252_; lean_object* v_toSeqRight_2253_; lean_object* v___f_2254_; lean_object* v___f_2255_; lean_object* v___f_2256_; lean_object* v___f_2257_; lean_object* v___x_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v_toApplicative_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2297_; 
v___x_2248_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2249_ = lean_ctor_get(v___x_2248_, 0);
v_toFunctor_2250_ = lean_ctor_get(v_toApplicative_2249_, 0);
v_toSeq_2251_ = lean_ctor_get(v_toApplicative_2249_, 2);
v_toSeqLeft_2252_ = lean_ctor_get(v_toApplicative_2249_, 3);
v_toSeqRight_2253_ = lean_ctor_get(v_toApplicative_2249_, 4);
v___f_2254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2255_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2250_, 2);
v___f_2256_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2256_, 0, v_toFunctor_2250_);
v___f_2257_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2257_, 0, v_toFunctor_2250_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___f_2256_);
lean_ctor_set(v___x_2258_, 1, v___f_2257_);
lean_inc(v_toSeqRight_2253_);
v___f_2259_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2259_, 0, v_toSeqRight_2253_);
lean_inc(v_toSeqLeft_2252_);
v___f_2260_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2260_, 0, v_toSeqLeft_2252_);
lean_inc(v_toSeq_2251_);
v___f_2261_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2261_, 0, v_toSeq_2251_);
v___x_2262_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2258_);
lean_ctor_set(v___x_2262_, 1, v___f_2254_);
lean_ctor_set(v___x_2262_, 2, v___f_2261_);
lean_ctor_set(v___x_2262_, 3, v___f_2260_);
lean_ctor_set(v___x_2262_, 4, v___f_2259_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v___f_2255_);
v___x_2264_ = l_StateRefT_x27_instMonad___redArg(v___x_2263_);
v_toApplicative_2265_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2297_ == 0)
{
lean_object* v_unused_2298_; 
v_unused_2298_ = lean_ctor_get(v___x_2264_, 1);
lean_dec(v_unused_2298_);
v___x_2267_ = v___x_2264_;
v_isShared_2268_ = v_isSharedCheck_2297_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_toApplicative_2265_);
lean_dec(v___x_2264_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2297_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_toFunctor_2269_; lean_object* v_toSeq_2270_; lean_object* v_toSeqLeft_2271_; lean_object* v_toSeqRight_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2295_; 
v_toFunctor_2269_ = lean_ctor_get(v_toApplicative_2265_, 0);
v_toSeq_2270_ = lean_ctor_get(v_toApplicative_2265_, 2);
v_toSeqLeft_2271_ = lean_ctor_get(v_toApplicative_2265_, 3);
v_toSeqRight_2272_ = lean_ctor_get(v_toApplicative_2265_, 4);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_toApplicative_2265_);
if (v_isSharedCheck_2295_ == 0)
{
lean_object* v_unused_2296_; 
v_unused_2296_ = lean_ctor_get(v_toApplicative_2265_, 1);
lean_dec(v_unused_2296_);
v___x_2274_ = v_toApplicative_2265_;
v_isShared_2275_ = v_isSharedCheck_2295_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_toSeqRight_2272_);
lean_inc(v_toSeqLeft_2271_);
lean_inc(v_toSeq_2270_);
lean_inc(v_toFunctor_2269_);
lean_dec(v_toApplicative_2265_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2295_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___f_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; lean_object* v___f_2282_; lean_object* v___f_2283_; lean_object* v___x_2285_; 
v___f_2276_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2277_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2269_);
v___f_2278_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2278_, 0, v_toFunctor_2269_);
v___f_2279_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2279_, 0, v_toFunctor_2269_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___f_2278_);
lean_ctor_set(v___x_2280_, 1, v___f_2279_);
v___f_2281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2281_, 0, v_toSeqRight_2272_);
v___f_2282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2282_, 0, v_toSeqLeft_2271_);
v___f_2283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2283_, 0, v_toSeq_2270_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 4, v___f_2281_);
lean_ctor_set(v___x_2274_, 3, v___f_2282_);
lean_ctor_set(v___x_2274_, 2, v___f_2283_);
lean_ctor_set(v___x_2274_, 1, v___f_2276_);
lean_ctor_set(v___x_2274_, 0, v___x_2280_);
v___x_2285_ = v___x_2274_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___f_2276_);
lean_ctor_set(v_reuseFailAlloc_2294_, 2, v___f_2283_);
lean_ctor_set(v_reuseFailAlloc_2294_, 3, v___f_2282_);
lean_ctor_set(v_reuseFailAlloc_2294_, 4, v___f_2281_);
v___x_2285_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2287_; 
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___f_2277_);
lean_ctor_set(v___x_2267_, 0, v___x_2285_);
v___x_2287_ = v___x_2267_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___f_2277_);
v___x_2287_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_23553__overap_2291_; lean_object* v___x_2292_; 
v___x_2288_ = l_StateRefT_x27_instMonad___redArg(v___x_2287_);
v___x_2289_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2290_ = l_instInhabitedOfMonad___redArg(v___x_2288_, v___x_2289_);
v___x_23553__overap_2291_ = lean_panic_fn_borrowed(v___x_2290_, v_msg_2241_);
lean_dec(v___x_2290_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
lean_inc(v___y_2244_);
lean_inc_ref(v___y_2243_);
lean_inc(v___y_2242_);
v___x_2292_ = lean_apply_6(v___x_23553__overap_2291_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, lean_box(0));
return v___x_2292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
return v_res_2306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
return v___x_2309_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2310_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2312_ = lean_unsigned_to_nat(0u);
v___x_2313_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
lean_ctor_set(v___x_2313_, 2, v___x_2312_);
lean_ctor_set(v___x_2313_, 3, v___x_2312_);
lean_ctor_set(v___x_2313_, 4, v___x_2311_);
lean_ctor_set(v___x_2313_, 5, v___x_2311_);
lean_ctor_set(v___x_2313_, 6, v___x_2311_);
lean_ctor_set(v___x_2313_, 7, v___x_2311_);
lean_ctor_set(v___x_2313_, 8, v___x_2311_);
lean_ctor_set(v___x_2313_, 9, v___x_2311_);
lean_ctor_set(v___x_2313_, 10, v___x_2311_);
lean_ctor_set(v___x_2313_, 11, v___x_2310_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_unsigned_to_nat(32u);
v___x_2315_ = lean_mk_empty_array_with_capacity(v___x_2314_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = ((size_t)5ULL);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_unsigned_to_nat(32u);
v___x_2320_ = lean_mk_empty_array_with_capacity(v___x_2319_);
v___x_2321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2322_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v___x_2320_);
lean_ctor_set(v___x_2322_, 2, v___x_2318_);
lean_ctor_set(v___x_2322_, 3, v___x_2318_);
lean_ctor_set_usize(v___x_2322_, 4, v___x_2317_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2323_ = lean_box(1);
v___x_2324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2325_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
lean_ctor_set(v___x_2326_, 1, v___x_2324_);
lean_ctor_set(v___x_2326_, 2, v___x_2323_);
return v___x_2326_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2329_ = l_Lean_stringToMessageData(v___x_2328_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2331_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2332_ = l_Lean_stringToMessageData(v___x_2331_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2334_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2338_ = l_Lean_stringToMessageData(v___x_2337_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2341_ = l_Lean_stringToMessageData(v___x_2340_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2344_ = l_Lean_stringToMessageData(v___x_2343_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__20));
v___x_2350_ = l_Lean_stringToMessageData(v___x_2349_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__22));
v___x_2353_ = l_Lean_stringToMessageData(v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__24));
v___x_2356_ = l_Lean_stringToMessageData(v___x_2355_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__26));
v___x_2359_ = l_Lean_stringToMessageData(v___x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2360_, lean_object* v_declHint_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_env_2366_; uint8_t v___x_2367_; 
v___x_2364_ = lean_box(0);
v___x_2365_ = lean_st_ref_get(v___y_2362_);
v_env_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc_ref(v_env_2366_);
lean_dec(v___x_2365_);
v___x_2367_ = l_Lean_Name_isAnonymous(v_declHint_2361_);
if (v___x_2367_ == 0)
{
uint8_t v_isExporting_2368_; 
v_isExporting_2368_ = lean_ctor_get_uint8(v_env_2366_, sizeof(void*)*13);
if (v_isExporting_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_dec_ref(v_env_2366_);
lean_dec(v_declHint_2361_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_msg_2360_);
return v___x_2369_;
}
else
{
lean_object* v___x_2370_; uint8_t v___x_2371_; 
lean_inc_ref(v_env_2366_);
v___x_2370_ = l_Lean_Environment_setExporting(v_env_2366_, v___x_2367_);
lean_inc(v_declHint_2361_);
lean_inc_ref(v___x_2370_);
v___x_2371_ = l_Lean_Environment_contains(v___x_2370_, v_declHint_2361_, v_isExporting_2368_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; 
lean_dec_ref(v___x_2370_);
lean_dec_ref(v_env_2366_);
lean_dec(v_declHint_2361_);
v___x_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_msg_2360_);
return v___x_2372_;
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v_c_2378_; lean_object* v___x_2379_; 
v___x_2373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2374_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2375_ = l_Lean_Options_empty;
v___x_2376_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2370_);
lean_ctor_set(v___x_2376_, 1, v___x_2373_);
lean_ctor_set(v___x_2376_, 2, v___x_2374_);
lean_ctor_set(v___x_2376_, 3, v___x_2375_);
lean_inc(v_declHint_2361_);
v___x_2377_ = l_Lean_MessageData_ofConstName(v_declHint_2361_, v___x_2367_);
v_c_2378_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2378_, 0, v___x_2376_);
lean_ctor_set(v_c_2378_, 1, v___x_2377_);
v___x_2379_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2366_, v_declHint_2361_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec_ref(v_env_2366_);
lean_dec(v_declHint_2361_);
v___x_2380_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
lean_ctor_set(v___x_2381_, 1, v_c_2378_);
v___x_2382_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2381_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_MessageData_note(v___x_2383_);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v_msg_2360_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
else
{
lean_object* v_val_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2443_; 
v_val_2387_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2389_ = v___x_2379_;
v_isShared_2390_ = v_isSharedCheck_2443_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_val_2387_);
lean_dec(v___x_2379_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2443_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2391_; lean_object* v_modules_2392_; lean_object* v_moduleNames_2393_; lean_object* v_mod_2394_; uint8_t v___y_2396_; uint8_t v___x_2426_; 
v___x_2391_ = l_Lean_Environment_header(v_env_2366_);
lean_dec_ref(v_env_2366_);
v_modules_2392_ = lean_ctor_get(v___x_2391_, 3);
lean_inc_ref(v_modules_2392_);
v_moduleNames_2393_ = lean_ctor_get(v___x_2391_, 4);
lean_inc_ref(v_moduleNames_2393_);
lean_dec_ref(v___x_2391_);
v_mod_2394_ = lean_array_get(v___x_2364_, v_moduleNames_2393_, v_val_2387_);
lean_dec_ref(v_moduleNames_2393_);
v___x_2426_ = l_Lean_isPrivateName(v_declHint_2361_);
lean_dec(v_declHint_2361_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2427_ = lean_array_get_size(v_modules_2392_);
v___x_2428_ = lean_nat_dec_lt(v_val_2387_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_dec_ref(v_modules_2392_);
lean_dec(v_val_2387_);
v___y_2396_ = v___x_2426_;
goto v___jp_2395_;
}
else
{
lean_object* v___x_2429_; lean_object* v_toImport_2430_; uint8_t v_isExported_2431_; 
v___x_2429_ = lean_array_fget(v_modules_2392_, v_val_2387_);
lean_dec(v_val_2387_);
lean_dec_ref(v_modules_2392_);
v_toImport_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc_ref(v_toImport_2430_);
lean_dec(v___x_2429_);
v_isExported_2431_ = lean_ctor_get_uint8(v_toImport_2430_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2430_);
v___y_2396_ = v_isExported_2431_;
goto v___jp_2395_;
}
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v_modules_2392_);
lean_del_object(v___x_2389_);
lean_dec(v_val_2387_);
v___x_2432_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2432_);
lean_ctor_set(v___x_2433_, 1, v_c_2378_);
v___x_2434_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = l_Lean_MessageData_ofName(v_mod_2394_);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2435_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2437_);
lean_ctor_set(v___x_2439_, 1, v___x_2438_);
v___x_2440_ = l_Lean_MessageData_note(v___x_2439_);
v___x_2441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_msg_2360_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
return v___x_2442_;
}
v___jp_2395_:
{
if (v___y_2396_ == 0)
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2397_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
lean_ctor_set(v___x_2398_, 1, v_c_2378_);
v___x_2399_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2398_);
lean_ctor_set(v___x_2400_, 1, v___x_2399_);
v___x_2401_ = l_Lean_MessageData_ofName(v_mod_2394_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = l_Lean_MessageData_note(v___x_2404_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v_msg_2360_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2406_);
v___x_2408_ = v___x_2389_;
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
else
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2410_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v_c_2378_);
v___x_2412_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = l_Lean_MessageData_ofName(v_mod_2394_);
lean_inc_ref(v___x_2414_);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2413_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21);
v___x_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2415_);
lean_ctor_set(v___x_2417_, 1, v___x_2416_);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2414_);
v___x_2419_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23);
v___x_2420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2418_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = l_Lean_MessageData_note(v___x_2420_);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_msg_2360_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2422_);
v___x_2424_ = v___x_2389_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
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
lean_object* v___x_2444_; 
lean_dec_ref(v_env_2366_);
lean_dec(v_declHint_2361_);
v___x_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2444_, 0, v_msg_2360_);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2445_, lean_object* v_declHint_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2445_, v_declHint_2446_, v___y_2447_);
lean_dec(v___y_2447_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2450_, lean_object* v_declHint_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2468_; 
v___x_2458_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2450_, v_declHint_2451_, v___y_2456_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2463_ = l_Lean_unknownIdentifierMessageTag;
v___x_2464_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2464_);
v___x_2466_ = v___x_2461_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2469_, lean_object* v_declHint_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2469_, v_declHint_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_ref_2484_; lean_object* v___x_2485_; lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2494_; 
v_ref_2484_ = lean_ctor_get(v___y_2481_, 2);
v___x_2485_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2494_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2494_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
lean_inc(v_ref_2484_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v_ref_2484_);
lean_ctor_set(v___x_2490_, 1, v_a_2486_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 1);
lean_ctor_set(v___x_2488_, 0, v___x_2490_);
v___x_2492_ = v___x_2488_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2502_, lean_object* v_msg_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_toCold_2510_; lean_object* v_currRecDepth_2511_; lean_object* v_ref_2512_; uint16_t v_optionFlags_2513_; uint8_t v_suppressElabErrors_2514_; uint8_t v_isRecordingDeps_2515_; lean_object* v_ref_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v_toCold_2510_ = lean_ctor_get(v___y_2507_, 0);
v_currRecDepth_2511_ = lean_ctor_get(v___y_2507_, 1);
v_ref_2512_ = lean_ctor_get(v___y_2507_, 2);
v_optionFlags_2513_ = lean_ctor_get_uint16(v___y_2507_, sizeof(void*)*3);
v_suppressElabErrors_2514_ = lean_ctor_get_uint8(v___y_2507_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2515_ = lean_ctor_get_uint8(v___y_2507_, sizeof(void*)*3 + 3);
v_ref_2516_ = l_Lean_replaceRef(v_ref_2502_, v_ref_2512_);
lean_inc(v_currRecDepth_2511_);
lean_inc_ref(v_toCold_2510_);
v___x_2517_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2517_, 0, v_toCold_2510_);
lean_ctor_set(v___x_2517_, 1, v_currRecDepth_2511_);
lean_ctor_set(v___x_2517_, 2, v_ref_2516_);
lean_ctor_set_uint16(v___x_2517_, sizeof(void*)*3, v_optionFlags_2513_);
lean_ctor_set_uint8(v___x_2517_, sizeof(void*)*3 + 2, v_suppressElabErrors_2514_);
lean_ctor_set_uint8(v___x_2517_, sizeof(void*)*3 + 3, v_isRecordingDeps_2515_);
v___x_2518_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2503_, v___y_2505_, v___y_2506_, v___x_2517_, v___y_2508_);
lean_dec_ref_known(v___x_2517_, 3);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2519_, lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2519_, v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec(v_ref_2519_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2528_, lean_object* v_msg_2529_, lean_object* v_declHint_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___x_2537_; lean_object* v_a_2538_; lean_object* v___x_2539_; 
v___x_2537_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2529_, v_declHint_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2528_, v_a_2538_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2540_, lean_object* v_msg_2541_, lean_object* v_declHint_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2540_, v_msg_2541_, v_declHint_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
lean_dec(v___y_2545_);
lean_dec_ref(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec(v_ref_2540_);
return v_res_2549_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2556_, lean_object* v_constName_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2564_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2565_ = 0;
lean_inc(v_constName_2557_);
v___x_2566_ = l_Lean_MessageData_ofConstName(v_constName_2557_, v___x_2565_);
v___x_2567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2564_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2556_, v___x_2569_, v_constName_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2571_, lean_object* v_constName_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2571_, v_constName_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v_ref_2571_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v_ref_2587_; lean_object* v___x_2588_; 
v_ref_2587_ = lean_ctor_get(v___y_2584_, 2);
v___x_2588_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2587_, v_constName_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; lean_object* v_env_2605_; uint8_t v___x_2606_; lean_object* v___x_2607_; 
v___x_2604_ = lean_st_ref_get(v___y_2602_);
v_env_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc_ref(v_env_2605_);
lean_dec(v___x_2604_);
v___x_2606_ = 0;
lean_inc(v_constName_2597_);
v___x_2607_ = l_Lean_Environment_find_x3f(v_env_2605_, v_constName_2597_, v___x_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2608_;
}
else
{
lean_object* v_val_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_constName_2597_);
v_val_2609_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2607_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_val_2609_);
lean_dec(v___x_2607_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set_tag(v___x_2611_, 0);
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_val_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v_res_2624_; 
v_res_2624_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
return v_res_2624_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2628_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2629_ = lean_unsigned_to_nat(53u);
v___x_2630_ = lean_unsigned_to_nat(62u);
v___x_2631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2632_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2633_ = l_mkPanicMessageWithDecl(v___x_2632_, v___x_2631_, v___x_2630_, v___x_2629_, v___x_2628_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2634_, size_t v_i_2635_, lean_object* v_bs_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
uint8_t v___x_2643_; 
v___x_2643_ = lean_usize_dec_lt(v_i_2635_, v_sz_2634_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_bs_2636_);
return v___x_2644_;
}
else
{
lean_object* v_v_2645_; lean_object* v___x_2646_; lean_object* v_bs_x27_2647_; lean_object* v_a_2649_; lean_object* v___x_2654_; 
v_v_2645_ = lean_array_uget(v_bs_2636_, v_i_2635_);
v___x_2646_ = lean_unsigned_to_nat(0u);
v_bs_x27_2647_ = lean_array_uset(v_bs_2636_, v_i_2635_, v___x_2646_);
v___x_2654_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2645_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
if (lean_obj_tag(v_a_2655_) == 6)
{
lean_object* v_val_2656_; lean_object* v_numFields_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; 
v_val_2656_ = lean_ctor_get(v_a_2655_, 0);
lean_inc_ref(v_val_2656_);
lean_dec_ref_known(v_a_2655_, 1);
v_numFields_2657_ = lean_ctor_get(v_val_2656_, 4);
lean_inc(v_numFields_2657_);
lean_dec_ref(v_val_2656_);
v___x_2658_ = 0;
v___x_2659_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2659_, 0, v_numFields_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2646_);
lean_ctor_set_uint8(v___x_2659_, sizeof(void*)*2, v___x_2658_);
v_a_2649_ = v___x_2659_;
goto v___jp_2648_;
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec(v_a_2655_);
v___x_2660_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2661_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2660_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v_a_2649_ = v_a_2662_;
goto v___jp_2648_;
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v_bs_x27_2647_);
v_a_2663_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2661_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2661_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v_bs_x27_2647_);
v_a_2671_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2654_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2654_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
v___jp_2648_:
{
size_t v___x_2650_; size_t v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = ((size_t)1ULL);
v___x_2651_ = lean_usize_add(v_i_2635_, v___x_2650_);
v___x_2652_ = lean_array_uset(v_bs_x27_2647_, v_i_2635_, v_a_2649_);
v_i_2635_ = v___x_2651_;
v_bs_2636_ = v___x_2652_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2679_, lean_object* v_i_2680_, lean_object* v_bs_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
size_t v_sz_boxed_2688_; size_t v_i_boxed_2689_; lean_object* v_res_2690_; 
v_sz_boxed_2688_ = lean_unbox_usize(v_sz_2679_);
lean_dec(v_sz_2679_);
v_i_boxed_2689_ = lean_unbox_usize(v_i_2680_);
lean_dec(v_i_2680_);
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2688_, v_i_boxed_2689_, v_bs_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_unsigned_to_nat(16u);
v___x_2693_ = lean_mk_array(v___x_2692_, v___x_2691_);
return v___x_2693_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2694_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2695_ = lean_unsigned_to_nat(0u);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
lean_ctor_set(v___x_2696_, 1, v___x_2694_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2699_, uint8_t v_alsoCasesOn_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
uint8_t v___x_2710_; 
v___x_2710_ = l_Lean_Expr_isApp(v_e_2699_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec_ref(v_e_2699_);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
return v___x_2712_;
}
else
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_Expr_getAppFn(v_e_2699_);
if (lean_obj_tag(v___x_2713_) == 4)
{
lean_object* v_declName_2714_; lean_object* v_us_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2870_; 
v_declName_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc_n(v_declName_2714_, 2);
v_us_2715_ = lean_ctor_get(v___x_2713_, 1);
lean_inc(v_us_2715_);
lean_dec_ref_known(v___x_2713_, 2);
v___x_2716_ = l_Lean_instInhabitedExpr;
v___x_2717_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2714_, v___y_2705_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2870_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2870_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
if (lean_obj_tag(v_a_2718_) == 1)
{
lean_object* v_val_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2763_; 
v_val_2722_ = lean_ctor_get(v_a_2718_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_a_2718_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2724_ = v_a_2718_;
v_isShared_2725_ = v_isSharedCheck_2763_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_val_2722_);
lean_dec(v_a_2718_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2763_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_dummy_2726_; lean_object* v_nargs_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v_args_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_dummy_2726_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2727_ = l_Lean_Expr_getAppNumArgs(v_e_2699_);
lean_inc(v_nargs_2727_);
v___x_2728_ = lean_mk_array(v_nargs_2727_, v_dummy_2726_);
v___x_2729_ = lean_unsigned_to_nat(1u);
v___x_2730_ = lean_nat_sub(v_nargs_2727_, v___x_2729_);
lean_dec(v_nargs_2727_);
v_args_2731_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2699_, v___x_2728_, v___x_2730_);
v___x_2732_ = lean_array_get_size(v_args_2731_);
v___x_2733_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2722_);
v___x_2734_ = lean_nat_dec_lt(v___x_2732_, v___x_2733_);
lean_dec(v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v_numParams_2735_; lean_object* v_numDiscrs_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
v_numParams_2735_ = lean_ctor_get(v_val_2722_, 0);
v_numDiscrs_2736_ = lean_ctor_get(v_val_2722_, 1);
v___x_2737_ = lean_array_mk(v_us_2715_);
v___x_2738_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2735_);
v___x_2739_ = l_Array_extract___redArg(v_args_2731_, v___x_2738_, v_numParams_2735_);
v___x_2740_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2722_);
v___x_2741_ = lean_array_get(v___x_2716_, v_args_2731_, v___x_2740_);
lean_dec(v___x_2740_);
v___x_2742_ = lean_nat_add(v_numParams_2735_, v___x_2729_);
v___x_2743_ = lean_nat_add(v___x_2742_, v_numDiscrs_2736_);
lean_inc(v___x_2743_);
lean_inc_ref_n(v_args_2731_, 2);
v___x_2744_ = l_Array_toSubarray___redArg(v_args_2731_, v___x_2742_, v___x_2743_);
v___x_2745_ = l_Subarray_copy___redArg(v___x_2744_);
v___x_2746_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2722_);
v___x_2747_ = lean_nat_add(v___x_2743_, v___x_2746_);
lean_dec(v___x_2746_);
lean_inc(v___x_2747_);
v___x_2748_ = l_Array_toSubarray___redArg(v_args_2731_, v___x_2743_, v___x_2747_);
v___x_2749_ = l_Subarray_copy___redArg(v___x_2748_);
v___x_2750_ = l_Array_toSubarray___redArg(v_args_2731_, v___x_2747_, v___x_2732_);
v___x_2751_ = l_Subarray_copy___redArg(v___x_2750_);
v___x_2752_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2752_, 0, v_val_2722_);
lean_ctor_set(v___x_2752_, 1, v_declName_2714_);
lean_ctor_set(v___x_2752_, 2, v___x_2737_);
lean_ctor_set(v___x_2752_, 3, v___x_2739_);
lean_ctor_set(v___x_2752_, 4, v___x_2741_);
lean_ctor_set(v___x_2752_, 5, v___x_2745_);
lean_ctor_set(v___x_2752_, 6, v___x_2749_);
lean_ctor_set(v___x_2752_, 7, v___x_2751_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2752_);
v___x_2754_ = v___x_2724_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2756_; 
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2754_);
v___x_2756_ = v___x_2720_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
lean_object* v___x_2759_; lean_object* v___x_2761_; 
lean_dec_ref(v_args_2731_);
lean_del_object(v___x_2724_);
lean_dec(v_val_2722_);
lean_dec(v_us_2715_);
lean_dec(v_declName_2714_);
v___x_2759_ = lean_box(0);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2759_);
v___x_2761_ = v___x_2720_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v___x_2764_; 
lean_del_object(v___x_2720_);
lean_dec(v_a_2718_);
v___x_2764_ = lean_st_ref_get(v___y_2705_);
if (v_alsoCasesOn_2700_ == 0)
{
lean_dec(v___x_2764_);
lean_dec(v_us_2715_);
lean_dec(v_declName_2714_);
lean_dec_ref(v_e_2699_);
goto v___jp_2707_;
}
else
{
lean_object* v_env_2765_; uint8_t v___x_2766_; 
v_env_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc_ref(v_env_2765_);
lean_dec(v___x_2764_);
lean_inc(v_declName_2714_);
v___x_2766_ = l_Lean_isCasesOnRecursor(v_env_2765_, v_declName_2714_);
if (v___x_2766_ == 0)
{
lean_dec(v_us_2715_);
lean_dec(v_declName_2714_);
lean_dec_ref(v_e_2699_);
goto v___jp_2707_;
}
else
{
lean_object* v_indName_2767_; lean_object* v___x_2768_; 
v_indName_2767_ = l_Lean_Name_getPrefix(v_declName_2714_);
v___x_2768_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2767_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2861_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2861_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2861_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
if (lean_obj_tag(v_a_2769_) == 5)
{
lean_object* v_val_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2856_; 
v_val_2773_ = lean_ctor_get(v_a_2769_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_a_2769_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2775_ = v_a_2769_;
v_isShared_2776_ = v_isSharedCheck_2856_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_val_2773_);
lean_dec(v_a_2769_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2856_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_toConstantVal_2777_; lean_object* v_numParams_2778_; lean_object* v_numIndices_2779_; lean_object* v_ctors_2780_; lean_object* v_nargs_2781_; lean_object* v_dummy_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v_args_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v_toConstantVal_2777_ = lean_ctor_get(v_val_2773_, 0);
lean_inc_ref(v_toConstantVal_2777_);
v_numParams_2778_ = lean_ctor_get(v_val_2773_, 1);
lean_inc(v_numParams_2778_);
v_numIndices_2779_ = lean_ctor_get(v_val_2773_, 2);
lean_inc(v_numIndices_2779_);
v_ctors_2780_ = lean_ctor_get(v_val_2773_, 4);
lean_inc(v_ctors_2780_);
v_nargs_2781_ = l_Lean_Expr_getAppNumArgs(v_e_2699_);
v_dummy_2782_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2781_);
v___x_2783_ = lean_mk_array(v_nargs_2781_, v_dummy_2782_);
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = lean_nat_sub(v_nargs_2781_, v___x_2784_);
lean_dec(v_nargs_2781_);
v_args_2786_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2699_, v___x_2783_, v___x_2785_);
v___x_2787_ = lean_nat_add(v_numParams_2778_, v___x_2784_);
v___x_2788_ = lean_nat_add(v___x_2787_, v_numIndices_2779_);
v___x_2789_ = lean_nat_add(v___x_2788_, v___x_2784_);
lean_dec(v___x_2788_);
v___x_2790_ = l_Lean_InductiveVal_numCtors(v_val_2773_);
lean_dec_ref(v_val_2773_);
v___x_2791_ = lean_nat_add(v___x_2789_, v___x_2790_);
lean_dec(v___x_2790_);
v___x_2792_ = lean_array_get_size(v_args_2786_);
v___x_2793_ = lean_nat_dec_le(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2796_; 
lean_dec(v___x_2791_);
lean_dec(v___x_2789_);
lean_dec(v___x_2787_);
lean_dec_ref(v_args_2786_);
lean_dec(v_ctors_2780_);
lean_dec(v_numIndices_2779_);
lean_dec(v_numParams_2778_);
lean_dec_ref(v_toConstantVal_2777_);
lean_del_object(v___x_2775_);
lean_dec(v_us_2715_);
lean_dec(v_declName_2714_);
v___x_2794_ = lean_box(0);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2794_);
v___x_2796_ = v___x_2771_;
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
else
{
lean_object* v___x_2798_; lean_object* v_params_2799_; lean_object* v_motive_2800_; lean_object* v_discrs_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v_discrInfos_2804_; lean_object* v_alts_2805_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v_lower_2847_; lean_object* v_upper_2848_; uint8_t v___x_2855_; 
lean_del_object(v___x_2771_);
v___x_2798_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2778_);
lean_inc_ref_n(v_args_2786_, 3);
v_params_2799_ = l_Array_toSubarray___redArg(v_args_2786_, v___x_2798_, v_numParams_2778_);
v_motive_2800_ = lean_array_get(v___x_2716_, v_args_2786_, v_numParams_2778_);
lean_dec(v_numParams_2778_);
lean_inc(v___x_2789_);
v_discrs_2801_ = l_Array_toSubarray___redArg(v_args_2786_, v___x_2787_, v___x_2789_);
v___x_2802_ = lean_nat_add(v_numIndices_2779_, v___x_2784_);
lean_dec(v_numIndices_2779_);
v___x_2803_ = lean_box(0);
v_discrInfos_2804_ = lean_mk_array(v___x_2802_, v___x_2803_);
lean_inc(v___x_2791_);
v_alts_2805_ = l_Array_toSubarray___redArg(v_args_2786_, v___x_2789_, v___x_2791_);
v___x_2855_ = lean_nat_dec_le(v___x_2791_, v___x_2798_);
if (v___x_2855_ == 0)
{
v_lower_2847_ = v___x_2791_;
v_upper_2848_ = v___x_2792_;
goto v___jp_2846_;
}
else
{
lean_dec(v___x_2791_);
v_lower_2847_ = v___x_2798_;
v_upper_2848_ = v___x_2792_;
goto v___jp_2846_;
}
v___jp_2806_:
{
lean_object* v___x_2809_; size_t v_sz_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v___x_2809_ = lean_array_mk(v_ctors_2780_);
v_sz_2810_ = lean_array_size(v___x_2809_);
v___x_2811_ = ((size_t)0ULL);
v___x_2812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2810_, v___x_2811_, v___x_2809_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2837_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2837_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2837_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_start_2817_; lean_object* v_stop_2818_; lean_object* v_start_2819_; lean_object* v_stop_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2832_; 
v_start_2817_ = lean_ctor_get(v_params_2799_, 1);
v_stop_2818_ = lean_ctor_get(v_params_2799_, 2);
v_start_2819_ = lean_ctor_get(v_discrs_2801_, 1);
v_stop_2820_ = lean_ctor_get(v_discrs_2801_, 2);
v___x_2821_ = lean_nat_sub(v_stop_2818_, v_start_2817_);
v___x_2822_ = lean_nat_sub(v_stop_2820_, v_start_2819_);
v___x_2823_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2824_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2821_);
lean_ctor_set(v___x_2824_, 1, v___x_2822_);
lean_ctor_set(v___x_2824_, 2, v_a_2813_);
lean_ctor_set(v___x_2824_, 3, v___y_2808_);
lean_ctor_set(v___x_2824_, 4, v_discrInfos_2804_);
lean_ctor_set(v___x_2824_, 5, v___x_2823_);
v___x_2825_ = lean_array_mk(v_us_2715_);
v___x_2826_ = l_Subarray_copy___redArg(v_params_2799_);
v___x_2827_ = l_Subarray_copy___redArg(v_discrs_2801_);
v___x_2828_ = l_Subarray_copy___redArg(v_alts_2805_);
v___x_2829_ = l_Subarray_copy___redArg(v___y_2807_);
v___x_2830_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2824_);
lean_ctor_set(v___x_2830_, 1, v_declName_2714_);
lean_ctor_set(v___x_2830_, 2, v___x_2825_);
lean_ctor_set(v___x_2830_, 3, v___x_2826_);
lean_ctor_set(v___x_2830_, 4, v_motive_2800_);
lean_ctor_set(v___x_2830_, 5, v___x_2827_);
lean_ctor_set(v___x_2830_, 6, v___x_2828_);
lean_ctor_set(v___x_2830_, 7, v___x_2829_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set_tag(v___x_2775_, 1);
lean_ctor_set(v___x_2775_, 0, v___x_2830_);
v___x_2832_ = v___x_2775_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2830_);
v___x_2832_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
lean_object* v___x_2834_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2832_);
v___x_2834_ = v___x_2815_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_alts_2805_);
lean_dec_ref(v_discrInfos_2804_);
lean_dec_ref(v_discrs_2801_);
lean_dec(v_motive_2800_);
lean_dec_ref(v_params_2799_);
lean_del_object(v___x_2775_);
lean_dec(v_us_2715_);
lean_dec(v_declName_2714_);
v_a_2838_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2812_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2812_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
v___jp_2846_:
{
lean_object* v_levelParams_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v_levelParams_2849_ = lean_ctor_get(v_toConstantVal_2777_, 1);
lean_inc(v_levelParams_2849_);
lean_dec_ref(v_toConstantVal_2777_);
v___x_2850_ = l_Array_toSubarray___redArg(v_args_2786_, v_lower_2847_, v_upper_2848_);
v___x_2851_ = l_List_lengthTR___redArg(v_levelParams_2849_);
lean_dec(v_levelParams_2849_);
v___x_2852_ = l_List_lengthTR___redArg(v_us_2715_);
v___x_2853_ = lean_nat_dec_eq(v___x_2851_, v___x_2852_);
lean_dec(v___x_2852_);
lean_dec(v___x_2851_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; 
v___x_2854_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2807_ = v___x_2850_;
v___y_2808_ = v___x_2854_;
goto v___jp_2806_;
}
else
{
v___y_2807_ = v___x_2850_;
v___y_2808_ = v___x_2803_;
goto v___jp_2806_;
}
}
}
}
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_dec(v_a_2769_);
lean_dec(v_us_2715_);
lean_dec(v_declName_2714_);
lean_dec_ref(v_e_2699_);
v___x_2857_ = lean_box(0);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 0, v___x_2857_);
v___x_2859_ = v___x_2771_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_us_2715_);
lean_dec(v_declName_2714_);
lean_dec_ref(v_e_2699_);
v_a_2862_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2768_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2768_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
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
lean_dec_ref(v___x_2713_);
lean_dec_ref(v_e_2699_);
goto v___jp_2707_;
}
}
v___jp_2707_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2871_, lean_object* v_alsoCasesOn_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2879_; lean_object* v_res_2880_; 
v_alsoCasesOn_boxed_2879_ = lean_unbox(v_alsoCasesOn_2872_);
v_res_2880_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2871_, v_alsoCasesOn_boxed_2879_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
if (lean_obj_tag(v_a_2881_) == 0)
{
lean_object* v___x_2883_; 
v___x_2883_ = l_List_reverse___redArg(v_a_2882_);
return v___x_2883_;
}
else
{
lean_object* v_head_2884_; lean_object* v_tail_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2894_; 
v_head_2884_ = lean_ctor_get(v_a_2881_, 0);
v_tail_2885_ = lean_ctor_get(v_a_2881_, 1);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_a_2881_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2887_ = v_a_2881_;
v_isShared_2888_ = v_isSharedCheck_2894_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_tail_2885_);
lean_inc(v_head_2884_);
lean_dec(v_a_2881_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2894_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2889_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_MessageData_ofExpr(v_head_2884_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 1, v_a_2882_);
lean_ctor_set(v___x_2887_, 0, v___x_2889_);
v___x_2891_ = v___x_2887_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2889_);
lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_a_2882_);
v___x_2891_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
v_a_2881_ = v_tail_2885_;
v_a_2882_ = v___x_2891_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2895_, lean_object* v_x_2896_){
_start:
{
lean_object* v_fnName_2897_; uint8_t v___x_2898_; 
v_fnName_2897_ = lean_ctor_get(v_x_2896_, 0);
v___x_2898_ = l_Lean_Expr_isConstOf(v_x_2895_, v_fnName_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2899_, lean_object* v_x_2900_){
_start:
{
uint8_t v_res_2901_; lean_object* v_r_2902_; 
v_res_2901_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2899_, v_x_2900_);
lean_dec_ref(v_x_2900_);
lean_dec_ref(v_x_2899_);
v_r_2902_ = lean_box(v_res_2901_);
return v_r_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2903_, lean_object* v_type_2904_, lean_object* v_val_2905_, lean_object* v_k_2906_, uint8_t v_nondep_2907_, uint8_t v_kind_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___f_2915_; lean_object* v___x_2916_; 
lean_inc(v___y_2909_);
v___f_2915_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2915_, 0, v_k_2906_);
lean_closure_set(v___f_2915_, 1, v___y_2909_);
v___x_2916_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2903_, v_type_2904_, v_val_2905_, v___f_2915_, v_nondep_2907_, v_kind_2908_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2916_) == 0)
{
return v___x_2916_;
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2925_, lean_object* v_type_2926_, lean_object* v_val_2927_, lean_object* v_k_2928_, lean_object* v_nondep_2929_, lean_object* v_kind_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v_nondep_boxed_2937_; uint8_t v_kind_boxed_2938_; lean_object* v_res_2939_; 
v_nondep_boxed_2937_ = lean_unbox(v_nondep_2929_);
v_kind_boxed_2938_ = lean_unbox(v_kind_2930_);
v_res_2939_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2925_, v_type_2926_, v_val_2927_, v_k_2928_, v_nondep_boxed_2937_, v_kind_boxed_2938_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_2940_, uint8_t v_usedLetOnly_2941_, lean_object* v_x_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; 
lean_inc(v___y_2947_);
lean_inc_ref(v___y_2946_);
lean_inc(v___y_2945_);
lean_inc_ref(v___y_2944_);
lean_inc(v___y_2943_);
lean_inc_ref(v_x_2942_);
v___x_2949_ = lean_apply_7(v_k_2940_, v_x_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_, lean_box(0));
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; uint8_t v___x_2954_; uint8_t v___x_2955_; lean_object* v___x_2956_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_mk_empty_array_with_capacity(v___x_2951_);
v___x_2953_ = lean_array_push(v___x_2952_, v_x_2942_);
v___x_2954_ = 0;
v___x_2955_ = 1;
v___x_2956_ = l_Lean_Meta_mkLetFVars(v___x_2953_, v_a_2950_, v_usedLetOnly_2941_, v___x_2954_, v___x_2955_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec_ref(v___x_2953_);
return v___x_2956_;
}
else
{
lean_dec_ref(v_x_2942_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_2957_, lean_object* v_usedLetOnly_2958_, lean_object* v_x_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
uint8_t v_usedLetOnly_boxed_2966_; lean_object* v_res_2967_; 
v_usedLetOnly_boxed_2966_ = lean_unbox(v_usedLetOnly_2958_);
v_res_2967_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_2957_, v_usedLetOnly_boxed_2966_, v_x_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_2968_, lean_object* v_type_2969_, lean_object* v_val_2970_, lean_object* v_k_2971_, uint8_t v_nondep_2972_, uint8_t v_kind_2973_, uint8_t v_usedLetOnly_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; lean_object* v___f_2982_; lean_object* v___x_2983_; 
v___x_2981_ = lean_box(v_usedLetOnly_2974_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2982_, 0, v_k_2971_);
lean_closure_set(v___f_2982_, 1, v___x_2981_);
v___x_2983_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2968_, v_type_2969_, v_val_2970_, v___f_2982_, v_nondep_2972_, v_kind_2973_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_2984_, lean_object* v_type_2985_, lean_object* v_val_2986_, lean_object* v_k_2987_, lean_object* v_nondep_2988_, lean_object* v_kind_2989_, lean_object* v_usedLetOnly_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
uint8_t v_nondep_boxed_2997_; uint8_t v_kind_boxed_2998_; uint8_t v_usedLetOnly_boxed_2999_; lean_object* v_res_3000_; 
v_nondep_boxed_2997_ = lean_unbox(v_nondep_2988_);
v_kind_boxed_2998_ = lean_unbox(v_kind_2989_);
v_usedLetOnly_boxed_2999_ = lean_unbox(v_usedLetOnly_2990_);
v_res_3000_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_2984_, v_type_2985_, v_val_2986_, v_k_2987_, v_nondep_boxed_2997_, v_kind_boxed_2998_, v_usedLetOnly_boxed_2999_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3001_, lean_object* v_positions_3002_, lean_object* v_recFnNames_3003_, lean_object* v_containsRecFn_3004_, lean_object* v_below_3005_, size_t v_sz_3006_, size_t v_i_3007_, lean_object* v_bs_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
uint8_t v___x_3015_; 
v___x_3015_ = lean_usize_dec_lt(v_i_3007_, v_sz_3006_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
lean_dec_ref(v_below_3005_);
lean_dec_ref(v_containsRecFn_3004_);
lean_dec_ref(v_recFnNames_3003_);
lean_dec_ref(v_positions_3002_);
lean_dec_ref(v_recArgInfos_3001_);
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_bs_3008_);
return v___x_3016_;
}
else
{
lean_object* v_v_3017_; lean_object* v___x_3018_; lean_object* v_bs_x27_3019_; lean_object* v___x_3020_; 
v_v_3017_ = lean_array_uget(v_bs_3008_, v_i_3007_);
v___x_3018_ = lean_unsigned_to_nat(0u);
v_bs_x27_3019_ = lean_array_uset(v_bs_3008_, v_i_3007_, v___x_3018_);
lean_inc_ref(v___y_3012_);
lean_inc_ref(v_below_3005_);
lean_inc_ref(v_containsRecFn_3004_);
lean_inc_ref(v_recFnNames_3003_);
lean_inc_ref(v_positions_3002_);
lean_inc_ref(v_recArgInfos_3001_);
v___x_3020_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3001_, v_positions_3002_, v_recFnNames_3003_, v_containsRecFn_3004_, v_below_3005_, v_v_3017_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; size_t v___x_3022_; size_t v___x_3023_; lean_object* v___x_3024_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = ((size_t)1ULL);
v___x_3023_ = lean_usize_add(v_i_3007_, v___x_3022_);
v___x_3024_ = lean_array_uset(v_bs_x27_3019_, v_i_3007_, v_a_3021_);
v_i_3007_ = v___x_3023_;
v_bs_3008_ = v___x_3024_;
goto _start;
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_bs_x27_3019_);
lean_dec_ref(v_below_3005_);
lean_dec_ref(v_containsRecFn_3004_);
lean_dec_ref(v_recFnNames_3003_);
lean_dec_ref(v_positions_3002_);
lean_dec_ref(v_recArgInfos_3001_);
v_a_3026_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_3020_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_3020_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3036_ = l_Lean_stringToMessageData(v___x_3035_);
return v___x_3036_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3039_ = l_Lean_stringToMessageData(v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3040_, lean_object* v_positions_3041_, lean_object* v_recFnNames_3042_, lean_object* v_containsRecFn_3043_, lean_object* v_below_3044_, lean_object* v_e_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_, lean_object* v_x_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_){
_start:
{
if (lean_obj_tag(v_x_3046_) == 5)
{
lean_object* v_fn_3055_; lean_object* v_arg_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_fn_3055_ = lean_ctor_get(v_x_3046_, 0);
lean_inc_ref(v_fn_3055_);
v_arg_3056_ = lean_ctor_get(v_x_3046_, 1);
lean_inc_ref(v_arg_3056_);
lean_dec_ref_known(v_x_3046_, 2);
v___x_3057_ = lean_array_set(v_x_3047_, v_x_3048_, v_arg_3056_);
v___x_3058_ = lean_unsigned_to_nat(1u);
v___x_3059_ = lean_nat_sub(v_x_3048_, v___x_3058_);
lean_dec(v_x_3048_);
v_x_3046_ = v_fn_3055_;
v_x_3047_ = v___x_3057_;
v_x_3048_ = v___x_3059_;
goto _start;
}
else
{
lean_object* v___f_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_dec(v_x_3048_);
lean_inc_ref(v_x_3046_);
v___f_3061_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3061_, 0, v_x_3046_);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3061_, v_recArgInfos_3040_, v___x_3062_);
if (lean_obj_tag(v___x_3063_) == 1)
{
lean_object* v_val_3064_; lean_object* v___x_3065_; lean_object* v___y_3067_; lean_object* v_recArgPos_3093_; lean_object* v_indGroupInst_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
lean_dec_ref(v_x_3046_);
v_val_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_val_3064_);
lean_dec_ref_known(v___x_3063_, 1);
v___x_3065_ = lean_array_fget_borrowed(v_recArgInfos_3040_, v_val_3064_);
v_recArgPos_3093_ = lean_ctor_get(v___x_3065_, 2);
v_indGroupInst_3094_ = lean_ctor_get(v___x_3065_, 4);
v___x_3095_ = lean_array_get_size(v_x_3047_);
v___x_3096_ = lean_nat_dec_lt(v_recArgPos_3093_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_dec(v_val_3064_);
lean_dec_ref(v_x_3047_);
lean_dec_ref(v_below_3044_);
lean_dec_ref(v_containsRecFn_3043_);
lean_dec_ref(v_recFnNames_3042_);
lean_dec_ref(v_positions_3041_);
lean_dec_ref(v_recArgInfos_3040_);
v___x_3097_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3098_ = l_Lean_indentExpr(v_e_3045_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3099_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_array_fget_borrowed(v_x_3047_, v_recArgPos_3093_);
lean_inc_ref(v___y_3052_);
lean_inc(v___x_3101_);
lean_inc_ref(v_below_3044_);
lean_inc_ref(v_containsRecFn_3043_);
lean_inc_ref(v_recFnNames_3042_);
lean_inc_ref(v_positions_3041_);
lean_inc_ref(v_recArgInfos_3040_);
v___x_3102_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3040_, v_positions_3041_, v_recFnNames_3042_, v_containsRecFn_3043_, v_below_3044_, v___x_3101_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v_params_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v_params_3104_ = lean_ctor_get(v_indGroupInst_3094_, 2);
v___x_3105_ = lean_array_get_size(v_params_3104_);
lean_inc_ref(v_positions_3041_);
lean_inc_ref(v_below_3044_);
v___x_3106_ = l_Lean_Elab_Structural_toBelow(v_below_3044_, v___x_3105_, v_positions_3041_, v_val_3064_, v_a_3103_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_dec_ref(v_e_3045_);
v___y_3067_ = v___x_3106_;
goto v___jp_3066_;
}
else
{
lean_object* v_a_3107_; uint8_t v___y_3109_; uint8_t v___x_3114_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v___x_3114_ = l_Lean_Exception_isInterrupt(v_a_3107_);
if (v___x_3114_ == 0)
{
uint8_t v___x_3115_; 
lean_inc(v_a_3107_);
v___x_3115_ = l_Lean_Exception_isRuntime(v_a_3107_);
v___y_3109_ = v___x_3115_;
goto v___jp_3108_;
}
else
{
v___y_3109_ = v___x_3114_;
goto v___jp_3108_;
}
v___jp_3108_:
{
if (v___y_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
lean_dec_ref_known(v___x_3106_, 1);
v___x_3110_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3111_ = l_Lean_indentExpr(v_e_3045_);
v___x_3112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3110_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3112_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
v___y_3067_ = v___x_3113_;
goto v___jp_3066_;
}
else
{
lean_dec_ref(v_e_3045_);
v___y_3067_ = v___x_3106_;
goto v___jp_3066_;
}
}
}
}
else
{
lean_dec(v_val_3064_);
lean_dec_ref(v_x_3047_);
lean_dec_ref(v_e_3045_);
lean_dec_ref(v_below_3044_);
lean_dec_ref(v_containsRecFn_3043_);
lean_dec_ref(v_recFnNames_3042_);
lean_dec_ref(v_positions_3041_);
lean_dec_ref(v_recArgInfos_3040_);
return v___x_3102_;
}
}
v___jp_3066_:
{
if (lean_obj_tag(v___y_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v_fixedParamPerm_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v_snd_3072_; size_t v_sz_3073_; size_t v___x_3074_; lean_object* v___x_3075_; 
v_a_3068_ = lean_ctor_get(v___y_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___y_3067_, 1);
v_fixedParamPerm_3069_ = lean_ctor_get(v___x_3065_, 1);
v___x_3070_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3069_, v_x_3047_);
lean_dec_ref(v_x_3047_);
lean_inc(v___x_3065_);
v___x_3071_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3065_, v___x_3070_);
v_snd_3072_ = lean_ctor_get(v___x_3071_, 1);
lean_inc(v_snd_3072_);
lean_dec_ref(v___x_3071_);
v_sz_3073_ = lean_array_size(v_snd_3072_);
v___x_3074_ = ((size_t)0ULL);
v___x_3075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3040_, v_positions_3041_, v_recFnNames_3042_, v_containsRecFn_3043_, v_below_3044_, v_sz_3073_, v___x_3074_, v_snd_3072_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3084_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3084_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = l_Lean_mkAppN(v_a_3068_, v_a_3076_);
lean_dec(v_a_3076_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3080_);
v___x_3082_ = v___x_3078_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec(v_a_3068_);
v_a_3085_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3075_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3075_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_dec_ref(v_x_3047_);
lean_dec_ref(v_below_3044_);
lean_dec_ref(v_containsRecFn_3043_);
lean_dec_ref(v_recFnNames_3042_);
lean_dec_ref(v_positions_3041_);
lean_dec_ref(v_recArgInfos_3040_);
return v___y_3067_;
}
}
}
else
{
lean_object* v___x_3116_; 
lean_dec(v___x_3063_);
lean_dec_ref(v_e_3045_);
lean_inc_ref(v___y_3052_);
lean_inc_ref(v_below_3044_);
lean_inc_ref(v_containsRecFn_3043_);
lean_inc_ref(v_recFnNames_3042_);
lean_inc_ref(v_positions_3041_);
lean_inc_ref(v_recArgInfos_3040_);
v___x_3116_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3040_, v_positions_3041_, v_recFnNames_3042_, v_containsRecFn_3043_, v_below_3044_, v_x_3046_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; size_t v_sz_3118_; size_t v___x_3119_; lean_object* v___x_3120_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v_sz_3118_ = lean_array_size(v_x_3047_);
v___x_3119_ = ((size_t)0ULL);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3040_, v_positions_3041_, v_recFnNames_3042_, v_containsRecFn_3043_, v_below_3044_, v_sz_3118_, v___x_3119_, v_x_3047_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3129_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3129_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3127_; 
v___x_3125_ = l_Lean_mkAppN(v_a_3117_, v_a_3121_);
lean_dec(v_a_3121_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3125_);
v___x_3127_ = v___x_3123_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3125_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v_a_3117_);
v_a_3130_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3120_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3120_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
else
{
lean_dec_ref(v_x_3047_);
lean_dec_ref(v_below_3044_);
lean_dec_ref(v_containsRecFn_3043_);
lean_dec_ref(v_recFnNames_3042_);
lean_dec_ref(v_positions_3041_);
lean_dec_ref(v_recArgInfos_3040_);
return v___x_3116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3138_, lean_object* v_recArgInfos_3139_, lean_object* v_positions_3140_, lean_object* v_recFnNames_3141_, lean_object* v_containsRecFn_3142_, lean_object* v_below_3143_, uint8_t v___x_3144_, uint8_t v_a_3145_, lean_object* v_x_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
v___x_3153_ = lean_expr_instantiate1(v_body_3138_, v_x_3146_);
lean_inc_ref(v___y_3150_);
v___x_3154_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3139_, v_positions_3140_, v_recFnNames_3141_, v_containsRecFn_3142_, v_below_3143_, v___x_3153_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = lean_unsigned_to_nat(1u);
v___x_3157_ = lean_mk_empty_array_with_capacity(v___x_3156_);
v___x_3158_ = lean_array_push(v___x_3157_, v_x_3146_);
v___x_3159_ = 1;
v___x_3160_ = l_Lean_Meta_mkLambdaFVars(v___x_3158_, v_a_3155_, v___x_3144_, v_a_3145_, v___x_3144_, v_a_3145_, v___x_3159_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec_ref(v___x_3158_);
return v___x_3160_;
}
else
{
lean_dec_ref(v_x_3146_);
return v___x_3154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3161_, lean_object* v_recArgInfos_3162_, lean_object* v_positions_3163_, lean_object* v_recFnNames_3164_, lean_object* v_containsRecFn_3165_, lean_object* v_below_3166_, lean_object* v___x_3167_, lean_object* v_a_3168_, lean_object* v_x_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v___x_28821__boxed_3176_; uint8_t v_a_28822__boxed_3177_; lean_object* v_res_3178_; 
v___x_28821__boxed_3176_ = lean_unbox(v___x_3167_);
v_a_28822__boxed_3177_ = lean_unbox(v_a_3168_);
v_res_3178_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3161_, v_recArgInfos_3162_, v_positions_3163_, v_recFnNames_3164_, v_containsRecFn_3165_, v_below_3166_, v___x_28821__boxed_3176_, v_a_28822__boxed_3177_, v_x_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v_body_3161_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3179_, lean_object* v_recArgInfos_3180_, lean_object* v_positions_3181_, lean_object* v_recFnNames_3182_, lean_object* v_containsRecFn_3183_, lean_object* v_below_3184_, uint8_t v___x_3185_, uint8_t v_a_3186_, lean_object* v_x_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_expr_instantiate1(v_body_3179_, v_x_3187_);
lean_inc_ref(v___y_3191_);
v___x_3195_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3180_, v_positions_3181_, v_recFnNames_3182_, v_containsRecFn_3183_, v_below_3184_, v___x_3194_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = lean_unsigned_to_nat(1u);
v___x_3198_ = lean_mk_empty_array_with_capacity(v___x_3197_);
v___x_3199_ = lean_array_push(v___x_3198_, v_x_3187_);
v___x_3200_ = 1;
v___x_3201_ = l_Lean_Meta_mkForallFVars(v___x_3199_, v_a_3196_, v___x_3185_, v_a_3186_, v_a_3186_, v___x_3200_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec_ref(v___x_3199_);
return v___x_3201_;
}
else
{
lean_dec_ref(v_x_3187_);
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3202_, lean_object* v_recArgInfos_3203_, lean_object* v_positions_3204_, lean_object* v_recFnNames_3205_, lean_object* v_containsRecFn_3206_, lean_object* v_below_3207_, lean_object* v___x_3208_, lean_object* v_a_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
uint8_t v___x_28839__boxed_3217_; uint8_t v_a_28840__boxed_3218_; lean_object* v_res_3219_; 
v___x_28839__boxed_3217_ = lean_unbox(v___x_3208_);
v_a_28840__boxed_3218_ = lean_unbox(v_a_3209_);
v_res_3219_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3202_, v_recArgInfos_3203_, v_positions_3204_, v_recFnNames_3205_, v_containsRecFn_3206_, v_below_3207_, v___x_28839__boxed_3217_, v_a_28840__boxed_3218_, v_x_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v_body_3202_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3220_, lean_object* v_recArgInfos_3221_, lean_object* v_positions_3222_, lean_object* v_recFnNames_3223_, lean_object* v_containsRecFn_3224_, lean_object* v_below_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3220_, v_recArgInfos_3221_, v_positions_3222_, v_recFnNames_3223_, v_containsRecFn_3224_, v_below_3225_, v_x_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v_x_3226_);
lean_dec_ref(v_body_3220_);
return v_res_3233_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3238_ = l_Lean_stringToMessageData(v___x_3237_);
return v___x_3238_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3241_ = l_Lean_stringToMessageData(v___x_3240_);
return v___x_3241_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3247_ = l_Lean_stringToMessageData(v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3248_, lean_object* v_b_3249_, lean_object* v_recArgInfos_3250_, lean_object* v_positions_3251_, lean_object* v_recFnNames_3252_, lean_object* v_containsRecFn_3253_, uint8_t v___x_3254_, uint8_t v_a_3255_, lean_object* v___x_3256_, lean_object* v_a_3257_, lean_object* v_e_3258_, lean_object* v___x_3259_, lean_object* v_xs_3260_, lean_object* v_altBody_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v_toCold_3303_; lean_object* v_options_3304_; uint8_t v_hasTrace_3305_; 
v_toCold_3303_ = lean_ctor_get(v___y_3265_, 0);
v_options_3304_ = lean_ctor_get(v_toCold_3303_, 2);
v_hasTrace_3305_ = lean_ctor_get_uint8(v_options_3304_, sizeof(void*)*1);
if (v_hasTrace_3305_ == 0)
{
lean_dec(v___x_3259_);
v___y_3280_ = v___y_3262_;
v___y_3281_ = v___y_3263_;
v___y_3282_ = v___y_3264_;
v___y_3283_ = v___y_3265_;
v___y_3284_ = v___y_3266_;
goto v___jp_3279_;
}
else
{
lean_object* v_inheritedTraceOptions_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; 
v_inheritedTraceOptions_3306_ = lean_ctor_get(v_toCold_3303_, 11);
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3259_);
v___x_3308_ = l_Lean_Name_append(v___x_3307_, v___x_3259_);
v___x_3309_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3306_, v_options_3304_, v___x_3308_);
lean_dec(v___x_3308_);
if (v___x_3309_ == 0)
{
lean_dec(v___x_3259_);
v___y_3280_ = v___y_3262_;
v___y_3281_ = v___y_3263_;
v___y_3282_ = v___y_3264_;
v___y_3283_ = v___y_3265_;
v___y_3284_ = v___y_3266_;
goto v___jp_3279_;
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3310_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3249_);
v___x_3311_ = l_Nat_reprFast(v_b_3249_);
v___x_3312_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
v___x_3313_ = l_Lean_MessageData_ofFormat(v___x_3312_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3310_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
lean_inc_ref(v_xs_3260_);
v___x_3317_ = lean_array_to_list(v_xs_3260_);
v___x_3318_ = lean_box(0);
v___x_3319_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3317_, v___x_3318_);
v___x_3320_ = l_Lean_MessageData_ofList(v___x_3319_);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3316_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3259_, v___x_3321_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_dec_ref_known(v___x_3322_, 1);
v___y_3280_ = v___y_3262_;
v___y_3281_ = v___y_3263_;
v___y_3282_ = v___y_3264_;
v___y_3283_ = v___y_3265_;
v___y_3284_ = v___y_3266_;
goto v___jp_3279_;
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v_altBody_3261_);
lean_dec_ref(v_xs_3260_);
lean_dec_ref(v_e_3258_);
lean_dec_ref(v_a_3257_);
lean_dec_ref(v_containsRecFn_3253_);
lean_dec_ref(v_recFnNames_3252_);
lean_dec_ref(v_positions_3251_);
lean_dec_ref(v_recArgInfos_3250_);
lean_dec(v_b_3249_);
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
v___jp_3268_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = lean_array_get_borrowed(v___x_3248_, v_xs_3260_, v_b_3249_);
lean_dec(v_b_3249_);
lean_inc_ref(v___y_3272_);
lean_inc(v___x_3274_);
v___x_3275_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3250_, v_positions_3251_, v_recFnNames_3252_, v_containsRecFn_3253_, v___x_3274_, v_altBody_3261_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v___x_3277_ = 1;
v___x_3278_ = l_Lean_Meta_mkLambdaFVars(v_xs_3260_, v_a_3276_, v___x_3254_, v_a_3255_, v___x_3254_, v_a_3255_, v___x_3277_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec_ref(v_xs_3260_);
return v___x_3278_;
}
else
{
lean_dec_ref(v_xs_3260_);
return v___x_3275_;
}
}
v___jp_3279_:
{
lean_object* v___x_3285_; uint8_t v___x_3286_; 
v___x_3285_ = lean_array_get_size(v_xs_3260_);
v___x_3286_ = lean_nat_dec_eq(v___x_3285_, v___x_3256_);
if (v___x_3286_ == 0)
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref(v_altBody_3261_);
lean_dec_ref(v_xs_3260_);
lean_dec_ref(v_containsRecFn_3253_);
lean_dec_ref(v_recFnNames_3252_);
lean_dec_ref(v_positions_3251_);
lean_dec_ref(v_recArgInfos_3250_);
lean_dec(v_b_3249_);
v___x_3287_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3288_ = l_Lean_indentExpr(v_a_3257_);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = l_Lean_indentExpr(v_e_3258_);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3293_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
else
{
lean_dec_ref(v_e_3258_);
lean_dec_ref(v_a_3257_);
v___y_3269_ = v___y_3280_;
v___y_3270_ = v___y_3281_;
v___y_3271_ = v___y_3282_;
v___y_3272_ = v___y_3283_;
v___y_3273_ = v___y_3284_;
goto v___jp_3268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3331_ = _args[0];
lean_object* v_b_3332_ = _args[1];
lean_object* v_recArgInfos_3333_ = _args[2];
lean_object* v_positions_3334_ = _args[3];
lean_object* v_recFnNames_3335_ = _args[4];
lean_object* v_containsRecFn_3336_ = _args[5];
lean_object* v___x_3337_ = _args[6];
lean_object* v_a_3338_ = _args[7];
lean_object* v___x_3339_ = _args[8];
lean_object* v_a_3340_ = _args[9];
lean_object* v_e_3341_ = _args[10];
lean_object* v___x_3342_ = _args[11];
lean_object* v_xs_3343_ = _args[12];
lean_object* v_altBody_3344_ = _args[13];
lean_object* v___y_3345_ = _args[14];
lean_object* v___y_3346_ = _args[15];
lean_object* v___y_3347_ = _args[16];
lean_object* v___y_3348_ = _args[17];
lean_object* v___y_3349_ = _args[18];
lean_object* v___y_3350_ = _args[19];
_start:
{
uint8_t v___x_28915__boxed_3351_; uint8_t v_a_28916__boxed_3352_; lean_object* v_res_3353_; 
v___x_28915__boxed_3351_ = lean_unbox(v___x_3337_);
v_a_28916__boxed_3352_ = lean_unbox(v_a_3338_);
v_res_3353_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3331_, v_b_3332_, v_recArgInfos_3333_, v_positions_3334_, v_recFnNames_3335_, v_containsRecFn_3336_, v___x_28915__boxed_3351_, v_a_28916__boxed_3352_, v___x_3339_, v_a_3340_, v_e_3341_, v___x_3342_, v_xs_3343_, v_altBody_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec(v___x_3339_);
lean_dec_ref(v___x_3331_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3354_, lean_object* v_positions_3355_, lean_object* v_recFnNames_3356_, lean_object* v_containsRecFn_3357_, uint8_t v_a_3358_, lean_object* v_e_3359_, lean_object* v_as_3360_, lean_object* v_bs_3361_, lean_object* v_i_3362_, lean_object* v_cs_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v___x_3370_; uint8_t v___x_3371_; 
v___x_3370_ = lean_array_get_size(v_as_3360_);
v___x_3371_ = lean_nat_dec_lt(v_i_3362_, v___x_3370_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; 
lean_dec(v_i_3362_);
lean_dec_ref(v_e_3359_);
lean_dec_ref(v_containsRecFn_3357_);
lean_dec_ref(v_recFnNames_3356_);
lean_dec_ref(v_positions_3355_);
lean_dec_ref(v_recArgInfos_3354_);
v___x_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_cs_3363_);
return v___x_3372_;
}
else
{
lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3373_ = lean_array_get_size(v_bs_3361_);
v___x_3374_ = lean_nat_dec_lt(v_i_3362_, v___x_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; 
lean_dec(v_i_3362_);
lean_dec_ref(v_e_3359_);
lean_dec_ref(v_containsRecFn_3357_);
lean_dec_ref(v_recFnNames_3356_);
lean_dec_ref(v_positions_3355_);
lean_dec_ref(v_recArgInfos_3354_);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v_cs_3363_);
return v___x_3375_;
}
else
{
lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; lean_object* v_a_3379_; lean_object* v_b_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___f_3385_; lean_object* v___x_3386_; 
v___x_3376_ = l_Lean_instInhabitedExpr;
v___x_3377_ = 0;
v___x_3378_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3379_ = lean_array_fget_borrowed(v_as_3360_, v_i_3362_);
v_b_3380_ = lean_array_fget_borrowed(v_bs_3361_, v_i_3362_);
v___x_3381_ = lean_unsigned_to_nat(1u);
v___x_3382_ = lean_nat_add(v_b_3380_, v___x_3381_);
v___x_3383_ = lean_box(v___x_3377_);
v___x_3384_ = lean_box(v_a_3358_);
lean_inc_ref(v_e_3359_);
lean_inc_n(v_a_3379_, 2);
lean_inc(v___x_3382_);
lean_inc_ref(v_containsRecFn_3357_);
lean_inc_ref(v_recFnNames_3356_);
lean_inc_ref(v_positions_3355_);
lean_inc_ref(v_recArgInfos_3354_);
lean_inc(v_b_3380_);
v___f_3385_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3385_, 0, v___x_3376_);
lean_closure_set(v___f_3385_, 1, v_b_3380_);
lean_closure_set(v___f_3385_, 2, v_recArgInfos_3354_);
lean_closure_set(v___f_3385_, 3, v_positions_3355_);
lean_closure_set(v___f_3385_, 4, v_recFnNames_3356_);
lean_closure_set(v___f_3385_, 5, v_containsRecFn_3357_);
lean_closure_set(v___f_3385_, 6, v___x_3383_);
lean_closure_set(v___f_3385_, 7, v___x_3384_);
lean_closure_set(v___f_3385_, 8, v___x_3382_);
lean_closure_set(v___f_3385_, 9, v_a_3379_);
lean_closure_set(v___f_3385_, 10, v_e_3359_);
lean_closure_set(v___f_3385_, 11, v___x_3378_);
v___x_3386_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3379_, v___x_3382_, v___f_3385_, v___x_3377_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3386_, 1);
v___x_3388_ = lean_nat_add(v_i_3362_, v___x_3381_);
lean_dec(v_i_3362_);
v___x_3389_ = lean_array_push(v_cs_3363_, v_a_3387_);
v_i_3362_ = v___x_3388_;
v_cs_3363_ = v___x_3389_;
goto _start;
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v_cs_3363_);
lean_dec(v_i_3362_);
lean_dec_ref(v_e_3359_);
lean_dec_ref(v_containsRecFn_3357_);
lean_dec_ref(v_recFnNames_3356_);
lean_dec_ref(v_positions_3355_);
lean_dec_ref(v_recArgInfos_3354_);
v_a_3391_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3386_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3386_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
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
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3408_, lean_object* v_positions_3409_, lean_object* v_recFnNames_3410_, lean_object* v_containsRecFn_3411_, lean_object* v_below_3412_, lean_object* v_e_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_e_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___x_3433_; 
lean_inc_ref(v_containsRecFn_3411_);
lean_inc(v_a_3418_);
lean_inc_ref(v_a_3417_);
lean_inc(v_a_3416_);
lean_inc_ref(v_a_3415_);
lean_inc(v_a_3414_);
lean_inc_ref(v_e_3413_);
v___x_3433_ = lean_apply_7(v_containsRecFn_3411_, v_e_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, lean_box(0));
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3648_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3648_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3648_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_unbox(v_a_3434_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3440_; 
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v_e_3413_);
v___x_3440_ = v___x_3436_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_e_3413_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
else
{
uint8_t v___x_3442_; 
lean_del_object(v___x_3436_);
v___x_3442_ = 0;
switch(lean_obj_tag(v_e_3413_))
{
case 6:
{
lean_object* v_binderName_3443_; lean_object* v_binderType_3444_; lean_object* v_body_3445_; uint8_t v_binderInfo_3446_; lean_object* v___x_3447_; lean_object* v___f_3448_; lean_object* v___x_3449_; 
v_binderName_3443_ = lean_ctor_get(v_e_3413_, 0);
lean_inc(v_binderName_3443_);
v_binderType_3444_ = lean_ctor_get(v_e_3413_, 1);
lean_inc_ref(v_binderType_3444_);
v_body_3445_ = lean_ctor_get(v_e_3413_, 2);
lean_inc_ref(v_body_3445_);
v_binderInfo_3446_ = lean_ctor_get_uint8(v_e_3413_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3413_, 3);
v___x_3447_ = lean_box(v___x_3442_);
lean_inc_ref(v_below_3412_);
lean_inc_ref(v_containsRecFn_3411_);
lean_inc_ref(v_recFnNames_3410_);
lean_inc_ref(v_positions_3409_);
lean_inc_ref(v_recArgInfos_3408_);
v___f_3448_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3448_, 0, v_body_3445_);
lean_closure_set(v___f_3448_, 1, v_recArgInfos_3408_);
lean_closure_set(v___f_3448_, 2, v_positions_3409_);
lean_closure_set(v___f_3448_, 3, v_recFnNames_3410_);
lean_closure_set(v___f_3448_, 4, v_containsRecFn_3411_);
lean_closure_set(v___f_3448_, 5, v_below_3412_);
lean_closure_set(v___f_3448_, 6, v___x_3447_);
lean_closure_set(v___f_3448_, 7, v_a_3434_);
lean_inc_ref(v_a_3417_);
v___x_3449_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v_below_3412_, v_binderType_3444_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
v___x_3451_ = 0;
v___x_3452_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3443_, v_binderInfo_3446_, v_a_3450_, v___f_3448_, v___x_3451_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec_ref(v_a_3417_);
return v___x_3452_;
}
else
{
lean_dec_ref(v___f_3448_);
lean_dec(v_binderName_3443_);
lean_dec_ref(v_a_3417_);
return v___x_3449_;
}
}
case 7:
{
lean_object* v_binderName_3453_; lean_object* v_binderType_3454_; lean_object* v_body_3455_; uint8_t v_binderInfo_3456_; lean_object* v___x_3457_; lean_object* v___f_3458_; lean_object* v___x_3459_; 
v_binderName_3453_ = lean_ctor_get(v_e_3413_, 0);
lean_inc(v_binderName_3453_);
v_binderType_3454_ = lean_ctor_get(v_e_3413_, 1);
lean_inc_ref(v_binderType_3454_);
v_body_3455_ = lean_ctor_get(v_e_3413_, 2);
lean_inc_ref(v_body_3455_);
v_binderInfo_3456_ = lean_ctor_get_uint8(v_e_3413_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3413_, 3);
v___x_3457_ = lean_box(v___x_3442_);
lean_inc_ref(v_below_3412_);
lean_inc_ref(v_containsRecFn_3411_);
lean_inc_ref(v_recFnNames_3410_);
lean_inc_ref(v_positions_3409_);
lean_inc_ref(v_recArgInfos_3408_);
v___f_3458_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3458_, 0, v_body_3455_);
lean_closure_set(v___f_3458_, 1, v_recArgInfos_3408_);
lean_closure_set(v___f_3458_, 2, v_positions_3409_);
lean_closure_set(v___f_3458_, 3, v_recFnNames_3410_);
lean_closure_set(v___f_3458_, 4, v_containsRecFn_3411_);
lean_closure_set(v___f_3458_, 5, v_below_3412_);
lean_closure_set(v___f_3458_, 6, v___x_3457_);
lean_closure_set(v___f_3458_, 7, v_a_3434_);
lean_inc_ref(v_a_3417_);
v___x_3459_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v_below_3412_, v_binderType_3454_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; uint8_t v___x_3461_; lean_object* v___x_3462_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3461_ = 0;
v___x_3462_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3453_, v_binderInfo_3456_, v_a_3460_, v___f_3458_, v___x_3461_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec_ref(v_a_3417_);
return v___x_3462_;
}
else
{
lean_dec_ref(v___f_3458_);
lean_dec(v_binderName_3453_);
lean_dec_ref(v_a_3417_);
return v___x_3459_;
}
}
case 8:
{
lean_object* v_declName_3463_; lean_object* v_type_3464_; lean_object* v_value_3465_; lean_object* v_body_3466_; uint8_t v_nondep_3467_; lean_object* v___f_3468_; lean_object* v___x_3469_; 
lean_dec(v_a_3434_);
v_declName_3463_ = lean_ctor_get(v_e_3413_, 0);
lean_inc(v_declName_3463_);
v_type_3464_ = lean_ctor_get(v_e_3413_, 1);
lean_inc_ref(v_type_3464_);
v_value_3465_ = lean_ctor_get(v_e_3413_, 2);
lean_inc_ref(v_value_3465_);
v_body_3466_ = lean_ctor_get(v_e_3413_, 3);
lean_inc_ref(v_body_3466_);
v_nondep_3467_ = lean_ctor_get_uint8(v_e_3413_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3413_, 4);
lean_inc_ref_n(v_below_3412_, 2);
lean_inc_ref_n(v_containsRecFn_3411_, 2);
lean_inc_ref_n(v_recFnNames_3410_, 2);
lean_inc_ref_n(v_positions_3409_, 2);
lean_inc_ref_n(v_recArgInfos_3408_, 2);
v___f_3468_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3468_, 0, v_body_3466_);
lean_closure_set(v___f_3468_, 1, v_recArgInfos_3408_);
lean_closure_set(v___f_3468_, 2, v_positions_3409_);
lean_closure_set(v___f_3468_, 3, v_recFnNames_3410_);
lean_closure_set(v___f_3468_, 4, v_containsRecFn_3411_);
lean_closure_set(v___f_3468_, 5, v_below_3412_);
lean_inc_ref(v_a_3417_);
v___x_3469_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v_below_3412_, v_type_3464_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; lean_object* v___x_3471_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
lean_inc_ref(v_a_3417_);
v___x_3471_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v_below_3412_, v_value_3465_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; uint8_t v___x_3473_; lean_object* v___x_3474_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___x_3473_ = 0;
v___x_3474_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3463_, v_a_3470_, v_a_3472_, v___f_3468_, v_nondep_3467_, v___x_3473_, v___x_3442_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec_ref(v_a_3417_);
return v___x_3474_;
}
else
{
lean_dec(v_a_3470_);
lean_dec_ref(v___f_3468_);
lean_dec(v_declName_3463_);
lean_dec_ref(v_a_3417_);
return v___x_3471_;
}
}
else
{
lean_dec_ref(v___f_3468_);
lean_dec_ref(v_value_3465_);
lean_dec(v_declName_3463_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
return v___x_3469_;
}
}
case 10:
{
lean_object* v_data_3475_; lean_object* v_expr_3476_; lean_object* v___x_3477_; 
lean_dec(v_a_3434_);
v_data_3475_ = lean_ctor_get(v_e_3413_, 0);
lean_inc(v_data_3475_);
v_expr_3476_ = lean_ctor_get(v_e_3413_, 1);
lean_inc_ref(v_expr_3476_);
v___x_3477_ = l_Lean_getRecAppSyntax_x3f(v_e_3413_);
lean_dec_ref_known(v_e_3413_, 2);
if (lean_obj_tag(v___x_3477_) == 1)
{
lean_object* v_val_3478_; lean_object* v_toCold_3479_; lean_object* v_currRecDepth_3480_; lean_object* v_ref_3481_; uint16_t v_optionFlags_3482_; uint8_t v_suppressElabErrors_3483_; uint8_t v_isRecordingDeps_3484_; lean_object* v_ref_3485_; lean_object* v___x_3486_; 
lean_dec(v_data_3475_);
v_val_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_val_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v_toCold_3479_ = lean_ctor_get(v_a_3417_, 0);
lean_inc_ref(v_toCold_3479_);
v_currRecDepth_3480_ = lean_ctor_get(v_a_3417_, 1);
lean_inc(v_currRecDepth_3480_);
v_ref_3481_ = lean_ctor_get(v_a_3417_, 2);
lean_inc(v_ref_3481_);
v_optionFlags_3482_ = lean_ctor_get_uint16(v_a_3417_, sizeof(void*)*3);
v_suppressElabErrors_3483_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3484_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_3417_);
v_ref_3485_ = l_Lean_replaceRef(v_val_3478_, v_ref_3481_);
lean_dec(v_ref_3481_);
lean_dec(v_val_3478_);
v___x_3486_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3486_, 0, v_toCold_3479_);
lean_ctor_set(v___x_3486_, 1, v_currRecDepth_3480_);
lean_ctor_set(v___x_3486_, 2, v_ref_3485_);
lean_ctor_set_uint16(v___x_3486_, sizeof(void*)*3, v_optionFlags_3482_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*3 + 2, v_suppressElabErrors_3483_);
lean_ctor_set_uint8(v___x_3486_, sizeof(void*)*3 + 3, v_isRecordingDeps_3484_);
v_e_3413_ = v_expr_3476_;
v_a_3417_ = v___x_3486_;
goto _start;
}
else
{
lean_object* v___x_3488_; 
lean_dec(v___x_3477_);
v___x_3488_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v_below_3412_, v_expr_3476_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3497_; 
v_a_3489_ = lean_ctor_get(v___x_3488_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3488_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3491_ = v___x_3488_;
v_isShared_3492_ = v_isSharedCheck_3497_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3488_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3497_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3493_ = l_Lean_mkMData(v_data_3475_, v_a_3489_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 0, v___x_3493_);
v___x_3495_ = v___x_3491_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
else
{
lean_dec(v_data_3475_);
return v___x_3488_;
}
}
}
case 11:
{
lean_object* v_typeName_3498_; lean_object* v_idx_3499_; lean_object* v_struct_3500_; lean_object* v___x_3501_; 
lean_dec(v_a_3434_);
v_typeName_3498_ = lean_ctor_get(v_e_3413_, 0);
lean_inc(v_typeName_3498_);
v_idx_3499_ = lean_ctor_get(v_e_3413_, 1);
lean_inc(v_idx_3499_);
v_struct_3500_ = lean_ctor_get(v_e_3413_, 2);
lean_inc_ref(v_struct_3500_);
lean_dec_ref_known(v_e_3413_, 3);
v___x_3501_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v_below_3412_, v_struct_3500_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3510_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3510_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3510_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3506_ = l_Lean_mkProj(v_typeName_3498_, v_idx_3499_, v_a_3502_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3506_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
else
{
lean_dec(v_idx_3499_);
lean_dec(v_typeName_3498_);
return v___x_3501_;
}
}
case 5:
{
uint8_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_unbox(v_a_3434_);
lean_inc_ref(v_e_3413_);
v___x_3512_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3413_, v___x_3511_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
if (lean_obj_tag(v_a_3513_) == 0)
{
lean_dec(v_a_3434_);
v_e_3421_ = v_e_3413_;
v___y_3422_ = v_a_3414_;
v___y_3423_ = v_a_3415_;
v___y_3424_ = v_a_3416_;
v___y_3425_ = v_a_3417_;
v___y_3426_ = v_a_3418_;
goto v___jp_3420_;
}
else
{
lean_object* v_val_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v_val_3514_ = lean_ctor_get(v_a_3513_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v_a_3513_, 1);
v___x_3515_ = lean_unsigned_to_nat(0u);
v___x_3516_ = lean_array_get_size(v_recArgInfos_3408_);
v___x_3517_ = lean_nat_dec_lt(v___x_3515_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_dec(v_val_3514_);
lean_dec(v_a_3434_);
v_e_3421_ = v_e_3413_;
v___y_3422_ = v_a_3414_;
v___y_3423_ = v_a_3415_;
v___y_3424_ = v_a_3416_;
v___y_3425_ = v_a_3417_;
v___y_3426_ = v_a_3418_;
goto v___jp_3420_;
}
else
{
if (v___x_3517_ == 0)
{
lean_dec(v_val_3514_);
lean_dec(v_a_3434_);
v_e_3421_ = v_e_3413_;
v___y_3422_ = v_a_3414_;
v___y_3423_ = v_a_3415_;
v___y_3424_ = v_a_3416_;
v___y_3425_ = v_a_3417_;
v___y_3426_ = v_a_3418_;
goto v___jp_3420_;
}
else
{
size_t v___x_3518_; size_t v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = ((size_t)0ULL);
v___x_3519_ = lean_usize_of_nat(v___x_3516_);
v___x_3520_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3413_, v_recArgInfos_3408_, v___x_3518_, v___x_3519_);
if (v___x_3520_ == 0)
{
lean_dec(v_val_3514_);
lean_dec(v_a_3434_);
v_e_3421_ = v_e_3413_;
v___y_3422_ = v_a_3414_;
v___y_3423_ = v_a_3415_;
v___y_3424_ = v_a_3416_;
v___y_3425_ = v_a_3417_;
v___y_3426_ = v_a_3418_;
goto v___jp_3420_;
}
else
{
lean_object* v_toCold_3521_; lean_object* v_inheritedTraceOptions_3522_; lean_object* v___x_3523_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___x_3594_; 
v_toCold_3521_ = lean_ctor_get(v_a_3417_, 0);
v_inheritedTraceOptions_3522_ = lean_ctor_get(v_toCold_3521_, 11);
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3594_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3523_, v_inheritedTraceOptions_3522_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; uint8_t v___x_3596_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = lean_unbox(v_a_3595_);
lean_dec(v_a_3595_);
if (v___x_3596_ == 0)
{
v___y_3525_ = v_a_3414_;
v___y_3526_ = v_a_3415_;
v___y_3527_ = v_a_3416_;
v___y_3528_ = v_a_3417_;
v___y_3529_ = v_a_3418_;
goto v___jp_3524_;
}
else
{
lean_object* v___x_3597_; 
lean_inc(v_a_3418_);
lean_inc_ref(v_a_3417_);
lean_inc(v_a_3416_);
lean_inc_ref(v_a_3415_);
lean_inc_ref(v_below_3412_);
v___x_3597_ = lean_infer_type(v_below_3412_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref_known(v___x_3597_, 1);
v___x_3599_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3412_);
v___x_3600_ = l_Lean_MessageData_ofExpr(v_below_3412_);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = l_Lean_MessageData_ofExpr(v_a_3598_);
v___x_3605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3603_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
v___x_3606_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3523_, v___x_3605_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_dec_ref_known(v___x_3606_, 1);
v___y_3525_ = v_a_3414_;
v___y_3526_ = v_a_3415_;
v___y_3527_ = v_a_3416_;
v___y_3528_ = v_a_3417_;
v___y_3529_ = v_a_3418_;
goto v___jp_3524_;
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec(v_val_3514_);
lean_dec_ref_known(v_e_3413_, 2);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
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
else
{
lean_dec(v_val_3514_);
lean_dec_ref_known(v_e_3413_, 2);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
return v___x_3597_;
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_val_3514_);
lean_dec_ref_known(v_e_3413_, 2);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
v_a_3615_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3594_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3594_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
v___jp_3524_:
{
lean_object* v___x_3530_; 
lean_inc_ref(v_below_3412_);
v___x_3530_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3514_, v_below_3412_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
if (lean_obj_tag(v_a_3531_) == 1)
{
lean_object* v_val_3532_; lean_object* v_toMatcherInfo_3533_; lean_object* v_matcherName_3534_; lean_object* v_matcherLevels_3535_; lean_object* v_params_3536_; lean_object* v_motive_3537_; lean_object* v_discrs_3538_; lean_object* v_alts_3539_; lean_object* v_remaining_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; lean_object* v___x_3544_; 
lean_dec_ref(v_below_3412_);
v_val_3532_ = lean_ctor_get(v_a_3531_, 0);
lean_inc(v_val_3532_);
lean_dec_ref_known(v_a_3531_, 1);
v_toMatcherInfo_3533_ = lean_ctor_get(v_val_3532_, 0);
lean_inc_ref(v_toMatcherInfo_3533_);
v_matcherName_3534_ = lean_ctor_get(v_val_3532_, 1);
lean_inc(v_matcherName_3534_);
v_matcherLevels_3535_ = lean_ctor_get(v_val_3532_, 2);
lean_inc_ref(v_matcherLevels_3535_);
v_params_3536_ = lean_ctor_get(v_val_3532_, 3);
lean_inc_ref(v_params_3536_);
v_motive_3537_ = lean_ctor_get(v_val_3532_, 4);
lean_inc_ref(v_motive_3537_);
v_discrs_3538_ = lean_ctor_get(v_val_3532_, 5);
lean_inc_ref(v_discrs_3538_);
v_alts_3539_ = lean_ctor_get(v_val_3532_, 6);
lean_inc_ref(v_alts_3539_);
v_remaining_3540_ = lean_ctor_get(v_val_3532_, 7);
lean_inc_ref(v_remaining_3540_);
v___x_3541_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3532_);
v___x_3542_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3543_ = lean_unbox(v_a_3434_);
lean_dec(v_a_3434_);
v___x_3544_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v___x_3543_, v_e_3413_, v_alts_3539_, v___x_3541_, v___x_3515_, v___x_3542_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec_ref(v___x_3541_);
lean_dec_ref(v_alts_3539_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3554_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3554_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3554_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3549_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3549_, 0, v_toMatcherInfo_3533_);
lean_ctor_set(v___x_3549_, 1, v_matcherName_3534_);
lean_ctor_set(v___x_3549_, 2, v_matcherLevels_3535_);
lean_ctor_set(v___x_3549_, 3, v_params_3536_);
lean_ctor_set(v___x_3549_, 4, v_motive_3537_);
lean_ctor_set(v___x_3549_, 5, v_discrs_3538_);
lean_ctor_set(v___x_3549_, 6, v_a_3545_);
lean_ctor_set(v___x_3549_, 7, v_remaining_3540_);
v___x_3550_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3549_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 0, v___x_3550_);
v___x_3552_ = v___x_3547_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec_ref(v_remaining_3540_);
lean_dec_ref(v_discrs_3538_);
lean_dec_ref(v_motive_3537_);
lean_dec_ref(v_params_3536_);
lean_dec_ref(v_matcherLevels_3535_);
lean_dec(v_matcherName_3534_);
lean_dec_ref(v_toMatcherInfo_3533_);
v_a_3555_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3544_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3544_);
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
lean_object* v_toCold_3563_; lean_object* v_inheritedTraceOptions_3564_; lean_object* v___x_3565_; 
lean_dec(v_a_3531_);
lean_dec(v_a_3434_);
v_toCold_3563_ = lean_ctor_get(v___y_3528_, 0);
v_inheritedTraceOptions_3564_ = lean_ctor_get(v_toCold_3563_, 11);
v___x_3565_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3523_, v_inheritedTraceOptions_3564_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; uint8_t v___x_3567_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v___x_3567_ = lean_unbox(v_a_3566_);
lean_dec(v_a_3566_);
if (v___x_3567_ == 0)
{
v_e_3421_ = v_e_3413_;
v___y_3422_ = v___y_3525_;
v___y_3423_ = v___y_3526_;
v___y_3424_ = v___y_3527_;
v___y_3425_ = v___y_3528_;
v___y_3426_ = v___y_3529_;
goto v___jp_3420_;
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3569_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3523_, v___x_3568_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_dec_ref_known(v___x_3569_, 1);
v_e_3421_ = v_e_3413_;
v___y_3422_ = v___y_3525_;
v___y_3423_ = v___y_3526_;
v___y_3424_ = v___y_3527_;
v___y_3425_ = v___y_3528_;
v___y_3426_ = v___y_3529_;
goto v___jp_3420_;
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v___y_3528_);
lean_dec_ref_known(v_e_3413_, 2);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
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
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec_ref(v___y_3528_);
lean_dec_ref_known(v_e_3413_, 2);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
v_a_3578_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3565_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3565_);
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
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec_ref(v___y_3528_);
lean_dec_ref_known(v_e_3413_, 2);
lean_dec(v_a_3434_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
v_a_3586_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3530_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3530_);
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
}
}
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref_known(v_e_3413_, 2);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
v_a_3623_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3512_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3512_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
default: 
{
lean_object* v___x_3631_; 
lean_dec(v_a_3434_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
lean_inc_ref(v_e_3413_);
v___x_3631_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3410_, v_e_3413_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
lean_dec_ref(v_a_3417_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v___x_3631_, 0);
lean_dec(v_unused_3639_);
v___x_3633_ = v___x_3631_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_dec(v___x_3631_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v_e_3413_);
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_e_3413_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v_e_3413_);
v_a_3640_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3631_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3631_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
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
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec_ref(v_a_3417_);
lean_dec_ref(v_e_3413_);
lean_dec_ref(v_below_3412_);
lean_dec_ref(v_containsRecFn_3411_);
lean_dec_ref(v_recFnNames_3410_);
lean_dec_ref(v_positions_3409_);
lean_dec_ref(v_recArgInfos_3408_);
v_a_3649_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3433_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3433_);
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
v___jp_3420_:
{
lean_object* v_dummy_3427_; lean_object* v_nargs_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_dummy_3427_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3428_ = l_Lean_Expr_getAppNumArgs(v_e_3421_);
lean_inc(v_nargs_3428_);
v___x_3429_ = lean_mk_array(v_nargs_3428_, v_dummy_3427_);
v___x_3430_ = lean_unsigned_to_nat(1u);
v___x_3431_ = lean_nat_sub(v_nargs_3428_, v___x_3430_);
lean_dec(v_nargs_3428_);
lean_inc_ref(v_e_3421_);
v___x_3432_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3408_, v_positions_3409_, v_recFnNames_3410_, v_containsRecFn_3411_, v_below_3412_, v_e_3421_, v_e_3421_, v___x_3429_, v___x_3431_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec_ref(v___y_3425_);
return v___x_3432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3657_, lean_object* v_recArgInfos_3658_, lean_object* v_positions_3659_, lean_object* v_recFnNames_3660_, lean_object* v_containsRecFn_3661_, lean_object* v_below_3662_, lean_object* v_x_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = lean_expr_instantiate1(v_body_3657_, v_x_3663_);
lean_inc_ref(v___y_3667_);
v___x_3671_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3658_, v_positions_3659_, v_recFnNames_3660_, v_containsRecFn_3661_, v_below_3662_, v___x_3670_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3672_, lean_object* v_positions_3673_, lean_object* v_recFnNames_3674_, lean_object* v_containsRecFn_3675_, lean_object* v_below_3676_, lean_object* v_sz_3677_, lean_object* v_i_3678_, lean_object* v_bs_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
size_t v_sz_boxed_3686_; size_t v_i_boxed_3687_; lean_object* v_res_3688_; 
v_sz_boxed_3686_ = lean_unbox_usize(v_sz_3677_);
lean_dec(v_sz_3677_);
v_i_boxed_3687_ = lean_unbox_usize(v_i_3678_);
lean_dec(v_i_3678_);
v_res_3688_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3672_, v_positions_3673_, v_recFnNames_3674_, v_containsRecFn_3675_, v_below_3676_, v_sz_boxed_3686_, v_i_boxed_3687_, v_bs_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_, v___y_3684_);
lean_dec(v___y_3684_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v___y_3681_);
lean_dec(v___y_3680_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3689_, lean_object* v_positions_3690_, lean_object* v_recFnNames_3691_, lean_object* v_containsRecFn_3692_, lean_object* v_a_3693_, lean_object* v_e_3694_, lean_object* v_as_3695_, lean_object* v_bs_3696_, lean_object* v_i_3697_, lean_object* v_cs_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
uint8_t v_a_28873__boxed_3705_; lean_object* v_res_3706_; 
v_a_28873__boxed_3705_ = lean_unbox(v_a_3693_);
v_res_3706_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3689_, v_positions_3690_, v_recFnNames_3691_, v_containsRecFn_3692_, v_a_28873__boxed_3705_, v_e_3694_, v_as_3695_, v_bs_3696_, v_i_3697_, v_cs_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v_bs_3696_);
lean_dec_ref(v_as_3695_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3707_, lean_object* v_positions_3708_, lean_object* v_recFnNames_3709_, lean_object* v_containsRecFn_3710_, lean_object* v_below_3711_, lean_object* v_e_3712_, lean_object* v_x_3713_, lean_object* v_x_3714_, lean_object* v_x_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3707_, v_positions_3708_, v_recFnNames_3709_, v_containsRecFn_3710_, v_below_3711_, v_e_3712_, v_x_3713_, v_x_3714_, v_x_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3723_, lean_object* v_positions_3724_, lean_object* v_recFnNames_3725_, lean_object* v_containsRecFn_3726_, lean_object* v_below_3727_, lean_object* v_e_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3723_, v_positions_3724_, v_recFnNames_3725_, v_containsRecFn_3726_, v_below_3727_, v_e_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_);
lean_dec(v_a_3733_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3736_, lean_object* v_msg_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3737_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3745_, lean_object* v_msg_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3745_, v_msg_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
lean_dec(v___y_3747_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3754_, lean_object* v_name_3755_, lean_object* v_type_3756_, lean_object* v_val_3757_, lean_object* v_k_3758_, uint8_t v_nondep_3759_, uint8_t v_kind_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3755_, v_type_3756_, v_val_3757_, v_k_3758_, v_nondep_3759_, v_kind_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3768_, lean_object* v_name_3769_, lean_object* v_type_3770_, lean_object* v_val_3771_, lean_object* v_k_3772_, lean_object* v_nondep_3773_, lean_object* v_kind_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
uint8_t v_nondep_boxed_3781_; uint8_t v_kind_boxed_3782_; lean_object* v_res_3783_; 
v_nondep_boxed_3781_ = lean_unbox(v_nondep_3773_);
v_kind_boxed_3782_ = lean_unbox(v_kind_3774_);
v_res_3783_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3768_, v_name_3769_, v_type_3770_, v_val_3771_, v_k_3772_, v_nondep_boxed_3781_, v_kind_boxed_3782_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3784_, v___y_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3800_, lean_object* v_msg_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3800_, v_msg_3801_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3809_, lean_object* v_msg_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3809_, v_msg_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3818_, lean_object* v_constName_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_){
_start:
{
lean_object* v___x_3826_; 
v___x_3826_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3827_, lean_object* v_constName_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3827_, v_constName_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3836_, lean_object* v_ref_3837_, lean_object* v_constName_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3837_, v_constName_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3846_, lean_object* v_ref_3847_, lean_object* v_constName_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3846_, v_ref_3847_, v_constName_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec(v_ref_3847_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3856_, lean_object* v_ref_3857_, lean_object* v_msg_3858_, lean_object* v_declHint_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v___x_3866_; 
v___x_3866_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3857_, v_msg_3858_, v_declHint_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3867_, lean_object* v_ref_3868_, lean_object* v_msg_3869_, lean_object* v_declHint_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3867_, v_ref_3868_, v_msg_3869_, v_declHint_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec(v_ref_3868_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3878_, lean_object* v_declHint_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3878_, v_declHint_3879_, v___y_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3887_, lean_object* v_declHint_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3887_, v_declHint_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3896_, lean_object* v_ref_3897_, lean_object* v_msg_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3897_, v_msg_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3906_, lean_object* v_ref_3907_, lean_object* v_msg_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3906_, v_ref_3907_, v_msg_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
lean_dec(v___y_3913_);
lean_dec_ref(v___y_3912_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec(v_ref_3907_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3916_, lean_object* v_e_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v_fst_3926_; lean_object* v_snd_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3924_ = lean_st_ref_take(v___y_3918_);
v___x_3925_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3916_, v_e_3917_, v___x_3924_);
v_fst_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_fst_3926_);
v_snd_3927_ = lean_ctor_get(v___x_3925_, 1);
lean_inc(v_snd_3927_);
lean_dec_ref(v___x_3925_);
v___x_3928_ = lean_st_ref_put(v___y_3918_, v_snd_3927_);
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_fst_3926_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_3930_, lean_object* v_e_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3930_, v_e_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
lean_dec(v___y_3936_);
lean_dec_ref(v___y_3935_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v_recFnNames_3930_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_3939_, size_t v_i_3940_, lean_object* v_bs_3941_){
_start:
{
uint8_t v___x_3942_; 
v___x_3942_ = lean_usize_dec_lt(v_i_3940_, v_sz_3939_);
if (v___x_3942_ == 0)
{
return v_bs_3941_;
}
else
{
lean_object* v_v_3943_; lean_object* v_fnName_3944_; lean_object* v___x_3945_; lean_object* v_bs_x27_3946_; size_t v___x_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v_v_3943_ = lean_array_uget_borrowed(v_bs_3941_, v_i_3940_);
v_fnName_3944_ = lean_ctor_get(v_v_3943_, 0);
lean_inc(v_fnName_3944_);
v___x_3945_ = lean_unsigned_to_nat(0u);
v_bs_x27_3946_ = lean_array_uset(v_bs_3941_, v_i_3940_, v___x_3945_);
v___x_3947_ = ((size_t)1ULL);
v___x_3948_ = lean_usize_add(v_i_3940_, v___x_3947_);
v___x_3949_ = lean_array_uset(v_bs_x27_3946_, v_i_3940_, v_fnName_3944_);
v_i_3940_ = v___x_3948_;
v_bs_3941_ = v___x_3949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_3951_, lean_object* v_i_3952_, lean_object* v_bs_3953_){
_start:
{
size_t v_sz_boxed_3954_; size_t v_i_boxed_3955_; lean_object* v_res_3956_; 
v_sz_boxed_3954_ = lean_unbox_usize(v_sz_3951_);
lean_dec(v_sz_3951_);
v_i_boxed_3955_ = lean_unbox_usize(v_i_3952_);
lean_dec(v_i_3952_);
v_res_3956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_3954_, v_i_boxed_3955_, v_bs_3953_);
return v_res_3956_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3957_ = lean_box(0);
v___x_3958_ = lean_unsigned_to_nat(16u);
v___x_3959_ = lean_mk_array(v___x_3958_, v___x_3957_);
return v___x_3959_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___x_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_3963_, lean_object* v_positions_3964_, lean_object* v_below_3965_, lean_object* v_e_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_){
_start:
{
size_t v_sz_3972_; size_t v___x_3973_; lean_object* v_recFnNames_3974_; lean_object* v_containsRecFn_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v_sz_3972_ = lean_array_size(v_recArgInfos_3963_);
v___x_3973_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_3963_);
v_recFnNames_3974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_3972_, v___x_3973_, v_recArgInfos_3963_);
lean_inc_ref(v_recFnNames_3974_);
v_containsRecFn_3975_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_3975_, 0, v_recFnNames_3974_);
v___x_3976_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_3977_ = lean_st_mk_ref(v___x_3976_);
lean_inc_ref(v_a_3969_);
v___x_3978_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3963_, v_positions_3964_, v_recFnNames_3974_, v_containsRecFn_3975_, v_below_3965_, v_e_3966_, v___x_3977_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3987_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3978_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3981_ = v___x_3978_;
v_isShared_3982_ = v_isSharedCheck_3987_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3978_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3987_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3983_ = lean_st_ref_get(v___x_3977_);
lean_dec(v___x_3977_);
lean_dec(v___x_3983_);
if (v_isShared_3982_ == 0)
{
v___x_3985_ = v___x_3981_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3979_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
else
{
lean_dec(v___x_3977_);
return v___x_3978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_3988_, lean_object* v_positions_3989_, lean_object* v_below_3990_, lean_object* v_e_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_3988_, v_positions_3989_, v_below_3990_, v_e_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_3998_, lean_object* v_k_3999_, uint8_t v_cleanupAnnotations_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___f_4006_; uint8_t v___x_4007_; uint8_t v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___f_4006_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4006_, 0, v_k_3999_);
v___x_4007_ = 1;
v___x_4008_ = 0;
v___x_4009_ = lean_box(0);
v___x_4010_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3998_, v___x_4007_, v___x_4008_, v___x_4007_, v___x_4008_, v___x_4009_, v___f_4006_, v_cleanupAnnotations_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4010_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4010_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
v_a_4019_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_4010_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4010_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4027_, lean_object* v_k_4028_, lean_object* v_cleanupAnnotations_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4035_; lean_object* v_res_4036_; 
v_cleanupAnnotations_boxed_4035_ = lean_unbox(v_cleanupAnnotations_4029_);
v_res_4036_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4027_, v_k_4028_, v_cleanupAnnotations_boxed_4035_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4037_, lean_object* v_e_4038_, lean_object* v_k_4039_, uint8_t v_cleanupAnnotations_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4038_, v_k_4039_, v_cleanupAnnotations_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4047_, lean_object* v_e_4048_, lean_object* v_k_4049_, lean_object* v_cleanupAnnotations_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4056_; lean_object* v_res_4057_; 
v_cleanupAnnotations_boxed_4056_ = lean_unbox(v_cleanupAnnotations_4050_);
v_res_4057_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4047_, v_e_4048_, v_k_4049_, v_cleanupAnnotations_boxed_4056_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4058_, lean_object* v_recArgInfo_4059_, lean_object* v_xs_4060_, lean_object* v___value_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_Meta_instantiateForall(v_type_4058_, v_xs_4060_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4069_; lean_object* v_fst_4070_; lean_object* v_snd_4071_; uint8_t v___x_4072_; uint8_t v___x_4073_; uint8_t v___x_4074_; lean_object* v___x_4075_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4069_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4059_, v_xs_4060_);
v_fst_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_fst_4070_);
v_snd_4071_ = lean_ctor_get(v___x_4069_, 1);
lean_inc(v_snd_4071_);
lean_dec_ref(v___x_4069_);
v___x_4072_ = 0;
v___x_4073_ = 1;
v___x_4074_ = 1;
v___x_4075_ = l_Lean_Meta_mkForallFVars(v_snd_4071_, v_a_4068_, v___x_4072_, v___x_4073_, v___x_4073_, v___x_4074_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v_snd_4071_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___x_4077_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc(v_a_4076_);
lean_dec_ref_known(v___x_4075_, 1);
v___x_4077_ = l_Lean_Meta_mkLambdaFVars(v_fst_4070_, v_a_4076_, v___x_4072_, v___x_4073_, v___x_4072_, v___x_4073_, v___x_4074_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v_fst_4070_);
return v___x_4077_;
}
else
{
lean_dec(v_fst_4070_);
return v___x_4075_;
}
}
else
{
lean_dec_ref(v_xs_4060_);
lean_dec_ref(v_recArgInfo_4059_);
return v___x_4067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4078_, lean_object* v_recArgInfo_4079_, lean_object* v_xs_4080_, lean_object* v___value_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4078_, v_recArgInfo_4079_, v_xs_4080_, v___value_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec_ref(v___value_4081_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4088_, lean_object* v_value_4089_, lean_object* v_type_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v___f_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; 
v___f_4096_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4096_, 0, v_type_4090_);
lean_closure_set(v___f_4096_, 1, v_recArgInfo_4088_);
v___x_4097_ = 0;
v___x_4098_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4089_, v___f_4096_, v___x_4097_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4099_, lean_object* v_value_4100_, lean_object* v_type_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4099_, v_value_4100_, v_type_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v_recArgInfos_4108_, lean_object* v_positions_4109_, lean_object* v_value_4110_, lean_object* v_fst_4111_, lean_object* v_snd_4112_, lean_object* v_below_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
lean_inc_ref(v_below_4113_);
v___x_4119_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4108_, v_positions_4109_, v_below_4113_, v_value_4110_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; uint8_t v___x_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4119_, 1);
v___x_4121_ = lean_unsigned_to_nat(1u);
v___x_4122_ = lean_mk_empty_array_with_capacity(v___x_4121_);
v___x_4123_ = lean_array_push(v___x_4122_, v_below_4113_);
v___x_4124_ = l_Array_append___redArg(v_fst_4111_, v___x_4123_);
lean_dec_ref(v___x_4123_);
v___x_4125_ = l_Array_append___redArg(v___x_4124_, v_snd_4112_);
v___x_4126_ = 0;
v___x_4127_ = 1;
v___x_4128_ = 1;
v___x_4129_ = l_Lean_Meta_mkLambdaFVars(v___x_4125_, v_a_4120_, v___x_4126_, v___x_4127_, v___x_4126_, v___x_4127_, v___x_4128_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec_ref(v___x_4125_);
return v___x_4129_;
}
else
{
lean_dec_ref(v_below_4113_);
lean_dec_ref(v_fst_4111_);
return v___x_4119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v_recArgInfos_4130_, lean_object* v_positions_4131_, lean_object* v_value_4132_, lean_object* v_fst_4133_, lean_object* v_snd_4134_, lean_object* v_below_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v_res_4141_; 
v_res_4141_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v_recArgInfos_4130_, v_positions_4131_, v_value_4132_, v_fst_4133_, v_snd_4134_, v_below_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec_ref(v_snd_4134_);
return v_res_4141_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4144_ = l_Lean_stringToMessageData(v___x_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4145_, lean_object* v_recArgInfos_4146_, lean_object* v_positions_4147_, lean_object* v_FType_4148_, lean_object* v_xs_4149_, lean_object* v_value_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___x_4156_; lean_object* v_fst_4157_; lean_object* v_snd_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4177_; 
v___x_4156_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4145_, v_xs_4149_);
v_fst_4157_ = lean_ctor_get(v___x_4156_, 0);
v_snd_4158_ = lean_ctor_get(v___x_4156_, 1);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4160_ = v___x_4156_;
v_isShared_4161_ = v_isSharedCheck_4177_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_snd_4158_);
lean_inc(v_fst_4157_);
lean_dec(v___x_4156_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4177_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___f_4162_; lean_object* v___x_4163_; 
lean_inc(v_fst_4157_);
v___f_4162_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4162_, 0, v_recArgInfos_4146_);
lean_closure_set(v___f_4162_, 1, v_positions_4147_);
lean_closure_set(v___f_4162_, 2, v_value_4150_);
lean_closure_set(v___f_4162_, 3, v_fst_4157_);
lean_closure_set(v___f_4162_, 4, v_snd_4158_);
v___x_4163_ = l_Lean_Meta_instantiateForall(v_FType_4148_, v_fst_4157_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v_fst_4157_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4165_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc_n(v_a_4164_, 2);
lean_dec_ref_known(v___x_4163_, 1);
v___x_4165_ = l_Lean_Meta_whnfForall(v_a_4164_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4165_, 1);
if (lean_obj_tag(v_a_4166_) == 7)
{
lean_object* v_binderName_4167_; lean_object* v_binderType_4168_; uint8_t v_binderInfo_4169_; lean_object* v___x_4170_; 
lean_dec(v_a_4164_);
lean_del_object(v___x_4160_);
v_binderName_4167_ = lean_ctor_get(v_a_4166_, 0);
lean_inc(v_binderName_4167_);
v_binderType_4168_ = lean_ctor_get(v_a_4166_, 1);
lean_inc_ref(v_binderType_4168_);
v_binderInfo_4169_ = lean_ctor_get_uint8(v_a_4166_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4166_, 3);
v___x_4170_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4167_, v_binderInfo_4169_, v_binderType_4168_, v___f_4162_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4170_;
}
else
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4174_; 
lean_dec(v_a_4166_);
lean_dec_ref(v___f_4162_);
v___x_4171_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1, &l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1);
v___x_4172_ = l_Lean_indentExpr(v_a_4164_);
if (v_isShared_4161_ == 0)
{
lean_ctor_set_tag(v___x_4160_, 7);
lean_ctor_set(v___x_4160_, 1, v___x_4172_);
lean_ctor_set(v___x_4160_, 0, v___x_4171_);
v___x_4174_ = v___x_4160_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4171_);
lean_ctor_set(v_reuseFailAlloc_4176_, 1, v___x_4172_);
v___x_4174_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4174_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4175_;
}
}
}
else
{
lean_dec(v_a_4164_);
lean_dec_ref(v___f_4162_);
lean_del_object(v___x_4160_);
return v___x_4165_;
}
}
else
{
lean_dec_ref(v___f_4162_);
lean_del_object(v___x_4160_);
return v___x_4163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4178_, lean_object* v_recArgInfos_4179_, lean_object* v_positions_4180_, lean_object* v_FType_4181_, lean_object* v_xs_4182_, lean_object* v_value_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4178_, v_recArgInfos_4179_, v_positions_4180_, v_FType_4181_, v_xs_4182_, v_value_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4190_, lean_object* v_positions_4191_, lean_object* v_recArgInfo_4192_, lean_object* v_value_4193_, lean_object* v_FType_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_){
_start:
{
lean_object* v___f_4200_; uint8_t v___x_4201_; lean_object* v___x_4202_; 
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4200_, 0, v_recArgInfo_4192_);
lean_closure_set(v___f_4200_, 1, v_recArgInfos_4190_);
lean_closure_set(v___f_4200_, 2, v_positions_4191_);
lean_closure_set(v___f_4200_, 3, v_FType_4194_);
v___x_4201_ = 0;
v___x_4202_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4193_, v___f_4200_, v___x_4201_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4203_, lean_object* v_positions_4204_, lean_object* v_recArgInfo_4205_, lean_object* v_value_4206_, lean_object* v_FType_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4203_, v_positions_4204_, v_recArgInfo_4205_, v_value_4206_, v_FType_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec_ref(v_a_4208_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4214_, lean_object* v_params_4215_, uint8_t v_isIndPred_4216_, lean_object* v_brecOnUniv_4217_, lean_object* v_levels_4218_, lean_object* v_idx_4219_){
_start:
{
lean_object* v_n_4220_; lean_object* v___y_4222_; 
v_n_4220_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4214_, v_idx_4219_);
if (v_isIndPred_4216_ == 0)
{
lean_object* v___x_4225_; 
v___x_4225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4225_, 0, v_brecOnUniv_4217_);
lean_ctor_set(v___x_4225_, 1, v_levels_4218_);
v___y_4222_ = v___x_4225_;
goto v___jp_4221_;
}
else
{
lean_dec(v_brecOnUniv_4217_);
v___y_4222_ = v_levels_4218_;
goto v___jp_4221_;
}
v___jp_4221_:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = l_Lean_Expr_const___override(v_n_4220_, v___y_4222_);
v___x_4224_ = l_Lean_mkAppN(v___x_4223_, v_params_4215_);
return v___x_4224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4226_, lean_object* v_params_4227_, lean_object* v_isIndPred_4228_, lean_object* v_brecOnUniv_4229_, lean_object* v_levels_4230_, lean_object* v_idx_4231_){
_start:
{
uint8_t v_isIndPred_boxed_4232_; lean_object* v_res_4233_; 
v_isIndPred_boxed_4232_ = lean_unbox(v_isIndPred_4228_);
v_res_4233_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4226_, v_params_4227_, v_isIndPred_boxed_4232_, v_brecOnUniv_4229_, v_levels_4230_, v_idx_4231_);
lean_dec(v_idx_4231_);
lean_dec_ref(v_params_4227_);
lean_dec_ref(v_toIndGroupInfo_4226_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4234_, lean_object* v_a_4235_, lean_object* v_n_4236_){
_start:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_apply_1(v_brecOnCons_4234_, v_n_4236_);
v___x_4238_ = l_Lean_mkAppN(v___x_4237_, v_a_4235_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4239_, lean_object* v_a_4240_, lean_object* v_n_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4239_, v_a_4240_, v_n_4241_);
lean_dec_ref(v_a_4240_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4243_, lean_object* v_type_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Meta_getLevel(v_type_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4251_, lean_object* v_type_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4251_, v_type_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
lean_dec(v___y_4256_);
lean_dec_ref(v___y_4255_);
lean_dec(v___y_4254_);
lean_dec_ref(v___y_4253_);
lean_dec_ref(v_x_4251_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4259_, size_t v_sz_4260_, size_t v_i_4261_, lean_object* v_bs_4262_){
_start:
{
uint8_t v___x_4263_; 
v___x_4263_ = lean_usize_dec_lt(v_i_4261_, v_sz_4260_);
if (v___x_4263_ == 0)
{
return v_bs_4262_;
}
else
{
lean_object* v___x_4264_; lean_object* v_v_4265_; lean_object* v___x_4266_; lean_object* v_bs_x27_4267_; lean_object* v___x_4268_; size_t v___x_4269_; size_t v___x_4270_; lean_object* v___x_4271_; 
v___x_4264_ = l_Lean_instInhabitedExpr;
v_v_4265_ = lean_array_uget(v_bs_4262_, v_i_4261_);
v___x_4266_ = lean_unsigned_to_nat(0u);
v_bs_x27_4267_ = lean_array_uset(v_bs_4262_, v_i_4261_, v___x_4266_);
v___x_4268_ = lean_array_get_borrowed(v___x_4264_, v_xs_4259_, v_v_4265_);
lean_dec(v_v_4265_);
v___x_4269_ = ((size_t)1ULL);
v___x_4270_ = lean_usize_add(v_i_4261_, v___x_4269_);
lean_inc(v___x_4268_);
v___x_4271_ = lean_array_uset(v_bs_x27_4267_, v_i_4261_, v___x_4268_);
v_i_4261_ = v___x_4270_;
v_bs_4262_ = v___x_4271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4273_, lean_object* v_sz_4274_, lean_object* v_i_4275_, lean_object* v_bs_4276_){
_start:
{
size_t v_sz_boxed_4277_; size_t v_i_boxed_4278_; lean_object* v_res_4279_; 
v_sz_boxed_4277_ = lean_unbox_usize(v_sz_4274_);
lean_dec(v_sz_4274_);
v_i_boxed_4278_ = lean_unbox_usize(v_i_4275_);
lean_dec(v_i_4275_);
v_res_4279_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4273_, v_sz_boxed_4277_, v_i_boxed_4278_, v_bs_4276_);
lean_dec_ref(v_xs_4273_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4280_, lean_object* v_f_4281_, lean_object* v_as_4282_, lean_object* v_bs_4283_, lean_object* v_i_4284_, lean_object* v_cs_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v___x_4291_; uint8_t v___x_4292_; 
v___x_4291_ = lean_array_get_size(v_as_4282_);
v___x_4292_ = lean_nat_dec_lt(v_i_4284_, v___x_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; 
lean_dec(v_i_4284_);
lean_dec_ref(v_f_4281_);
v___x_4293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4293_, 0, v_cs_4285_);
return v___x_4293_;
}
else
{
lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4294_ = lean_array_get_size(v_bs_4283_);
v___x_4295_ = lean_nat_dec_lt(v_i_4284_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; 
lean_dec(v_i_4284_);
lean_dec_ref(v_f_4281_);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v_cs_4285_);
return v___x_4296_;
}
else
{
lean_object* v_a_4297_; lean_object* v_b_4298_; size_t v_sz_4299_; size_t v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_a_4297_ = lean_array_fget_borrowed(v_as_4282_, v_i_4284_);
v_b_4298_ = lean_array_fget_borrowed(v_bs_4283_, v_i_4284_);
v_sz_4299_ = lean_array_size(v_b_4298_);
v___x_4300_ = ((size_t)0ULL);
lean_inc(v_b_4298_);
v___x_4301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4280_, v_sz_4299_, v___x_4300_, v_b_4298_);
lean_inc_ref(v_f_4281_);
lean_inc(v___y_4289_);
lean_inc_ref(v___y_4288_);
lean_inc(v___y_4287_);
lean_inc_ref(v___y_4286_);
lean_inc(v_a_4297_);
v___x_4302_ = lean_apply_7(v_f_4281_, v_a_4297_, v___x_4301_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, lean_box(0));
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = lean_unsigned_to_nat(1u);
v___x_4305_ = lean_nat_add(v_i_4284_, v___x_4304_);
lean_dec(v_i_4284_);
v___x_4306_ = lean_array_push(v_cs_4285_, v_a_4303_);
v_i_4284_ = v___x_4305_;
v_cs_4285_ = v___x_4306_;
goto _start;
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v_cs_4285_);
lean_dec(v_i_4284_);
lean_dec_ref(v_f_4281_);
v_a_4308_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4302_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4302_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4316_, lean_object* v_f_4317_, lean_object* v_as_4318_, lean_object* v_bs_4319_, lean_object* v_i_4320_, lean_object* v_cs_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4316_, v_f_4317_, v_as_4318_, v_bs_4319_, v_i_4320_, v_cs_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec_ref(v_bs_4319_);
lean_dec_ref(v_as_4318_);
lean_dec_ref(v_xs_4316_);
return v_res_4327_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Array_instInhabited___redArg();
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; lean_object* v_toApplicative_4336_; lean_object* v_toFunctor_4337_; lean_object* v_toSeq_4338_; lean_object* v_toSeqLeft_4339_; lean_object* v_toSeqRight_4340_; lean_object* v___f_4341_; lean_object* v___f_4342_; lean_object* v___f_4343_; lean_object* v___f_4344_; lean_object* v___x_4345_; lean_object* v___f_4346_; lean_object* v___f_4347_; lean_object* v___f_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v_toApplicative_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4383_; 
v___x_4335_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4336_ = lean_ctor_get(v___x_4335_, 0);
v_toFunctor_4337_ = lean_ctor_get(v_toApplicative_4336_, 0);
v_toSeq_4338_ = lean_ctor_get(v_toApplicative_4336_, 2);
v_toSeqLeft_4339_ = lean_ctor_get(v_toApplicative_4336_, 3);
v_toSeqRight_4340_ = lean_ctor_get(v_toApplicative_4336_, 4);
v___f_4341_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4342_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4337_, 2);
v___f_4343_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4343_, 0, v_toFunctor_4337_);
v___f_4344_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4344_, 0, v_toFunctor_4337_);
v___x_4345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4345_, 0, v___f_4343_);
lean_ctor_set(v___x_4345_, 1, v___f_4344_);
lean_inc(v_toSeqRight_4340_);
v___f_4346_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4346_, 0, v_toSeqRight_4340_);
lean_inc(v_toSeqLeft_4339_);
v___f_4347_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4347_, 0, v_toSeqLeft_4339_);
lean_inc(v_toSeq_4338_);
v___f_4348_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4348_, 0, v_toSeq_4338_);
v___x_4349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4345_);
lean_ctor_set(v___x_4349_, 1, v___f_4341_);
lean_ctor_set(v___x_4349_, 2, v___f_4348_);
lean_ctor_set(v___x_4349_, 3, v___f_4347_);
lean_ctor_set(v___x_4349_, 4, v___f_4346_);
v___x_4350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
lean_ctor_set(v___x_4350_, 1, v___f_4342_);
v___x_4351_ = l_StateRefT_x27_instMonad___redArg(v___x_4350_);
v_toApplicative_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4383_ == 0)
{
lean_object* v_unused_4384_; 
v_unused_4384_ = lean_ctor_get(v___x_4351_, 1);
lean_dec(v_unused_4384_);
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4383_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_toApplicative_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4383_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v_toFunctor_4356_; lean_object* v_toSeq_4357_; lean_object* v_toSeqLeft_4358_; lean_object* v_toSeqRight_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4381_; 
v_toFunctor_4356_ = lean_ctor_get(v_toApplicative_4352_, 0);
v_toSeq_4357_ = lean_ctor_get(v_toApplicative_4352_, 2);
v_toSeqLeft_4358_ = lean_ctor_get(v_toApplicative_4352_, 3);
v_toSeqRight_4359_ = lean_ctor_get(v_toApplicative_4352_, 4);
v_isSharedCheck_4381_ = !lean_is_exclusive(v_toApplicative_4352_);
if (v_isSharedCheck_4381_ == 0)
{
lean_object* v_unused_4382_; 
v_unused_4382_ = lean_ctor_get(v_toApplicative_4352_, 1);
lean_dec(v_unused_4382_);
v___x_4361_ = v_toApplicative_4352_;
v_isShared_4362_ = v_isSharedCheck_4381_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_toSeqRight_4359_);
lean_inc(v_toSeqLeft_4358_);
lean_inc(v_toSeq_4357_);
lean_inc(v_toFunctor_4356_);
lean_dec(v_toApplicative_4352_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4381_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v___f_4363_; lean_object* v___f_4364_; lean_object* v___f_4365_; lean_object* v___f_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; lean_object* v___f_4369_; lean_object* v___f_4370_; lean_object* v___x_4372_; 
v___f_4363_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4364_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4356_);
v___f_4365_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4365_, 0, v_toFunctor_4356_);
v___f_4366_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4366_, 0, v_toFunctor_4356_);
v___x_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___f_4365_);
lean_ctor_set(v___x_4367_, 1, v___f_4366_);
v___f_4368_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4368_, 0, v_toSeqRight_4359_);
v___f_4369_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4369_, 0, v_toSeqLeft_4358_);
v___f_4370_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4370_, 0, v_toSeq_4357_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 4, v___f_4368_);
lean_ctor_set(v___x_4361_, 3, v___f_4369_);
lean_ctor_set(v___x_4361_, 2, v___f_4370_);
lean_ctor_set(v___x_4361_, 1, v___f_4363_);
lean_ctor_set(v___x_4361_, 0, v___x_4367_);
v___x_4372_ = v___x_4361_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v___x_4367_);
lean_ctor_set(v_reuseFailAlloc_4380_, 1, v___f_4363_);
lean_ctor_set(v_reuseFailAlloc_4380_, 2, v___f_4370_);
lean_ctor_set(v_reuseFailAlloc_4380_, 3, v___f_4369_);
lean_ctor_set(v_reuseFailAlloc_4380_, 4, v___f_4368_);
v___x_4372_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
lean_object* v___x_4374_; 
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 1, v___f_4364_);
lean_ctor_set(v___x_4354_, 0, v___x_4372_);
v___x_4374_ = v___x_4354_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4379_, 1, v___f_4364_);
v___x_4374_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_855__overap_4377_; lean_object* v___x_4378_; 
v___x_4375_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4376_ = l_instInhabitedOfMonad___redArg(v___x_4374_, v___x_4375_);
v___x_855__overap_4377_ = lean_panic_fn_borrowed(v___x_4376_, v_msg_4329_);
lean_dec(v___x_4376_);
lean_inc(v___y_4333_);
lean_inc_ref(v___y_4332_);
lean_inc(v___y_4331_);
lean_inc_ref(v___y_4330_);
v___x_4378_ = lean_apply_5(v___x_855__overap_4377_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, lean_box(0));
return v___x_4378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
return v_res_4391_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4395_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4396_ = lean_unsigned_to_nat(2u);
v___x_4397_ = lean_unsigned_to_nat(73u);
v___x_4398_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4399_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4400_ = l_mkPanicMessageWithDecl(v___x_4399_, v___x_4398_, v___x_4397_, v___x_4396_, v___x_4395_);
return v___x_4400_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4402_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4403_ = lean_unsigned_to_nat(2u);
v___x_4404_ = lean_unsigned_to_nat(74u);
v___x_4405_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4406_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4407_ = l_mkPanicMessageWithDecl(v___x_4406_, v___x_4405_, v___x_4404_, v___x_4403_, v___x_4402_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4410_, lean_object* v_positions_4411_, lean_object* v_ys_4412_, lean_object* v_xs_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4419_ = lean_array_get_size(v_positions_4411_);
v___x_4420_ = lean_array_get_size(v_ys_4412_);
v___x_4421_ = lean_nat_dec_eq(v___x_4419_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_dec_ref(v_f_4410_);
v___x_4422_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4423_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4422_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
return v___x_4423_;
}
else
{
lean_object* v___x_4424_; lean_object* v___x_4425_; uint8_t v___x_4426_; 
v___x_4424_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4411_);
v___x_4425_ = lean_array_get_size(v_xs_4413_);
v___x_4426_ = lean_nat_dec_eq(v___x_4424_, v___x_4425_);
lean_dec(v___x_4424_);
if (v___x_4426_ == 0)
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
lean_dec_ref(v_f_4410_);
v___x_4427_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4428_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4427_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
return v___x_4428_;
}
else
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4429_ = lean_unsigned_to_nat(0u);
v___x_4430_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4431_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4413_, v_f_4410_, v_ys_4412_, v_positions_4411_, v___x_4429_, v___x_4430_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_);
return v___x_4431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4432_, lean_object* v_positions_4433_, lean_object* v_ys_4434_, lean_object* v_xs_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
lean_object* v_res_4441_; 
v_res_4441_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4432_, v_positions_4433_, v_ys_4434_, v_xs_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v_xs_4435_);
lean_dec_ref(v_ys_4434_);
lean_dec_ref(v_positions_4433_);
return v_res_4441_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
v___x_4443_ = lean_unsigned_to_nat(0u);
v___x_4444_ = l_Lean_Level_ofNat(v___x_4443_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4445_, lean_object* v_positions_4446_, lean_object* v_motives_4447_, uint8_t v_isIndPred_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v_indGroupInst_4457_; lean_object* v_brecOnUniv_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; 
v___x_4454_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4455_ = lean_unsigned_to_nat(0u);
v___x_4456_ = lean_array_get_borrowed(v___x_4454_, v_recArgInfos_4445_, v___x_4455_);
v_indGroupInst_4457_ = lean_ctor_get(v___x_4456_, 4);
if (v_isIndPred_4448_ == 0)
{
lean_object* v___f_4500_; lean_object* v___x_4501_; lean_object* v_motive_4502_; lean_object* v___x_4503_; 
v___f_4500_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4501_ = l_Lean_instInhabitedExpr;
v_motive_4502_ = lean_array_get_borrowed(v___x_4501_, v_motives_4447_, v___x_4455_);
lean_inc(v_motive_4502_);
v___x_4503_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4502_, v___f_4500_, v_isIndPred_4448_, v_a_4449_, v_a_4450_, v_a_4451_, v_a_4452_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref_known(v___x_4503_, 1);
v_brecOnUniv_4459_ = v_a_4504_;
v___y_4460_ = v_a_4449_;
v___y_4461_ = v_a_4450_;
v___y_4462_ = v_a_4451_;
v___y_4463_ = v_a_4452_;
goto v___jp_4458_;
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
v_a_4505_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4503_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4503_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
else
{
lean_object* v___x_4513_; 
v___x_4513_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4459_ = v___x_4513_;
v___y_4460_ = v_a_4449_;
v___y_4461_ = v_a_4450_;
v___y_4462_ = v_a_4451_;
v___y_4463_ = v_a_4452_;
goto v___jp_4458_;
}
v___jp_4458_:
{
lean_object* v_toIndGroupInfo_4464_; lean_object* v_levels_4465_; lean_object* v_params_4466_; lean_object* v___x_4467_; lean_object* v_brecOnCons_4468_; lean_object* v_brecOnAux_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v_toIndGroupInfo_4464_ = lean_ctor_get(v_indGroupInst_4457_, 0);
v_levels_4465_ = lean_ctor_get(v_indGroupInst_4457_, 1);
v_params_4466_ = lean_ctor_get(v_indGroupInst_4457_, 2);
v___x_4467_ = lean_box(v_isIndPred_4448_);
lean_inc_n(v_levels_4465_, 2);
lean_inc(v_brecOnUniv_4459_);
lean_inc_ref(v_params_4466_);
lean_inc_ref(v_toIndGroupInfo_4464_);
v_brecOnCons_4468_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4468_, 0, v_toIndGroupInfo_4464_);
lean_closure_set(v_brecOnCons_4468_, 1, v_params_4466_);
lean_closure_set(v_brecOnCons_4468_, 2, v___x_4467_);
lean_closure_set(v_brecOnCons_4468_, 3, v_brecOnUniv_4459_);
lean_closure_set(v_brecOnCons_4468_, 4, v_levels_4465_);
v_brecOnAux_4469_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4464_, v_params_4466_, v_isIndPred_4448_, v_brecOnUniv_4459_, v_levels_4465_, v___x_4455_);
v___x_4470_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4464_);
v___x_4471_ = l_Lean_Meta_inferArgumentTypesN(v___x_4470_, v_brecOnAux_4469_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
v___x_4473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4474_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4473_, v_positions_4446_, v_a_4472_, v_motives_4447_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec(v_a_4472_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4483_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4477_ = v___x_4474_;
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4474_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4483_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___f_4479_; lean_object* v___x_4481_; 
v___f_4479_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4479_, 0, v_brecOnCons_4468_);
lean_closure_set(v___f_4479_, 1, v_a_4475_);
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 0, v___f_4479_);
v___x_4481_ = v___x_4477_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___f_4479_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
lean_dec_ref(v_brecOnCons_4468_);
v_a_4484_ = lean_ctor_get(v___x_4474_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4474_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4474_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4474_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec_ref(v_brecOnCons_4468_);
v_a_4492_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4471_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4471_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4514_, lean_object* v_positions_4515_, lean_object* v_motives_4516_, lean_object* v_isIndPred_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
uint8_t v_isIndPred_boxed_4523_; lean_object* v_res_4524_; 
v_isIndPred_boxed_4523_ = lean_unbox(v_isIndPred_4517_);
v_res_4524_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4514_, v_positions_4515_, v_motives_4516_, v_isIndPred_boxed_4523_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec_ref(v_motives_4516_);
lean_dec_ref(v_positions_4515_);
lean_dec_ref(v_recArgInfos_4514_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4525_, lean_object* v_msg_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4533_, lean_object* v_msg_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4533_, v_msg_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4541_, lean_object* v_00_u03b1_4542_, lean_object* v_f_4543_, lean_object* v_positions_4544_, lean_object* v_ys_4545_, lean_object* v_xs_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4543_, v_positions_4544_, v_ys_4545_, v_xs_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4553_, lean_object* v_00_u03b1_4554_, lean_object* v_f_4555_, lean_object* v_positions_4556_, lean_object* v_ys_4557_, lean_object* v_xs_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4553_, v_00_u03b1_4554_, v_f_4555_, v_positions_4556_, v_ys_4557_, v_xs_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec_ref(v_xs_4558_);
lean_dec_ref(v_ys_4557_);
lean_dec_ref(v_positions_4556_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4565_, lean_object* v_00_u03b3_4566_, lean_object* v_xs_4567_, lean_object* v_f_4568_, lean_object* v_as_4569_, lean_object* v_bs_4570_, lean_object* v_i_4571_, lean_object* v_cs_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v___x_4578_; 
v___x_4578_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4567_, v_f_4568_, v_as_4569_, v_bs_4570_, v_i_4571_, v_cs_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
return v___x_4578_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4579_, lean_object* v_00_u03b3_4580_, lean_object* v_xs_4581_, lean_object* v_f_4582_, lean_object* v_as_4583_, lean_object* v_bs_4584_, lean_object* v_i_4585_, lean_object* v_cs_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4579_, v_00_u03b3_4580_, v_xs_4581_, v_f_4582_, v_as_4583_, v_bs_4584_, v_i_4585_, v_cs_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec_ref(v_bs_4584_);
lean_dec_ref(v_as_4583_);
lean_dec_ref(v_xs_4581_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(lean_object* v_type_4593_, lean_object* v_maxFVars_x3f_4594_, lean_object* v_k_4595_, uint8_t v_cleanupAnnotations_4596_, uint8_t v_whnfType_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
lean_object* v___f_4603_; lean_object* v___x_4604_; 
v___f_4603_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4603_, 0, v_k_4595_);
v___x_4604_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4593_, v_maxFVars_x3f_4594_, v___f_4603_, v_cleanupAnnotations_4596_, v_whnfType_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4604_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4604_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
return v___x_4610_;
}
}
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
v_a_4613_ = lean_ctor_get(v___x_4604_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4604_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4604_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4604_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg___boxed(lean_object* v_type_4621_, lean_object* v_maxFVars_x3f_4622_, lean_object* v_k_4623_, lean_object* v_cleanupAnnotations_4624_, lean_object* v_whnfType_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4631_; uint8_t v_whnfType_boxed_4632_; lean_object* v_res_4633_; 
v_cleanupAnnotations_boxed_4631_ = lean_unbox(v_cleanupAnnotations_4624_);
v_whnfType_boxed_4632_ = lean_unbox(v_whnfType_4625_);
v_res_4633_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4621_, v_maxFVars_x3f_4622_, v_k_4623_, v_cleanupAnnotations_boxed_4631_, v_whnfType_boxed_4632_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
lean_dec(v___y_4627_);
lean_dec_ref(v___y_4626_);
return v_res_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_00_u03b1_4634_, lean_object* v_type_4635_, lean_object* v_maxFVars_x3f_4636_, lean_object* v_k_4637_, uint8_t v_cleanupAnnotations_4638_, uint8_t v_whnfType_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4635_, v_maxFVars_x3f_4636_, v_k_4637_, v_cleanupAnnotations_4638_, v_whnfType_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_00_u03b1_4646_, lean_object* v_type_4647_, lean_object* v_maxFVars_x3f_4648_, lean_object* v_k_4649_, lean_object* v_cleanupAnnotations_4650_, lean_object* v_whnfType_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4657_; uint8_t v_whnfType_boxed_4658_; lean_object* v_res_4659_; 
v_cleanupAnnotations_boxed_4657_ = lean_unbox(v_cleanupAnnotations_4650_);
v_whnfType_boxed_4658_ = lean_unbox(v_whnfType_4651_);
v_res_4659_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_00_u03b1_4646_, v_type_4647_, v_maxFVars_x3f_4648_, v_k_4649_, v_cleanupAnnotations_boxed_4657_, v_whnfType_boxed_4658_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
return v_res_4659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v_numTypeFormers_4660_, lean_object* v_x_4661_, lean_object* v_brecOnType_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4660_, v_brecOnType_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed(lean_object* v_numTypeFormers_4669_, lean_object* v_x_4670_, lean_object* v_brecOnType_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v_res_4677_; 
v_res_4677_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(v_numTypeFormers_4669_, v_x_4670_, v_brecOnType_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec_ref(v_x_4670_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v___x_4678_, lean_object* v_e_4679_){
_start:
{
lean_object* v___x_4680_; lean_object* v___x_4681_; 
v___x_4680_ = l_Lean_indentD(v_e_4679_);
v___x_4681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4678_);
lean_ctor_set(v___x_4681_, 1, v___x_4680_);
return v___x_4681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4682_, lean_object* v_as_4683_, size_t v_sz_4684_, size_t v_i_4685_, lean_object* v_b_4686_){
_start:
{
uint8_t v___x_4688_; 
v___x_4688_ = lean_usize_dec_lt(v_i_4685_, v_sz_4684_);
if (v___x_4688_ == 0)
{
lean_object* v___x_4689_; 
lean_dec_ref(v_a_4682_);
v___x_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4689_, 0, v_b_4686_);
return v___x_4689_;
}
else
{
lean_object* v_a_4690_; lean_object* v___x_4691_; size_t v___x_4692_; size_t v___x_4693_; 
v_a_4690_ = lean_array_uget_borrowed(v_as_4683_, v_i_4685_);
lean_inc_ref(v_a_4682_);
v___x_4691_ = lean_array_set(v_b_4686_, v_a_4690_, v_a_4682_);
v___x_4692_ = ((size_t)1ULL);
v___x_4693_ = lean_usize_add(v_i_4685_, v___x_4692_);
v_i_4685_ = v___x_4693_;
v_b_4686_ = v___x_4691_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4695_, lean_object* v_as_4696_, lean_object* v_sz_4697_, lean_object* v_i_4698_, lean_object* v_b_4699_, lean_object* v___y_4700_){
_start:
{
size_t v_sz_boxed_4701_; size_t v_i_boxed_4702_; lean_object* v_res_4703_; 
v_sz_boxed_4701_ = lean_unbox_usize(v_sz_4697_);
lean_dec(v_sz_4697_);
v_i_boxed_4702_ = lean_unbox_usize(v_i_4698_);
lean_dec(v_i_4698_);
v_res_4703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4695_, v_as_4696_, v_sz_boxed_4701_, v_i_boxed_4702_, v_b_4699_);
lean_dec_ref(v_as_4696_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(lean_object* v_as_4704_, size_t v_sz_4705_, size_t v_i_4706_, lean_object* v_b_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
uint8_t v___x_4713_; 
v___x_4713_ = lean_usize_dec_lt(v_i_4706_, v_sz_4705_);
if (v___x_4713_ == 0)
{
lean_object* v___x_4714_; 
v___x_4714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4714_, 0, v_b_4707_);
return v___x_4714_;
}
else
{
lean_object* v_snd_4715_; lean_object* v_fst_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4760_; 
v_snd_4715_ = lean_ctor_get(v_b_4707_, 1);
v_fst_4716_ = lean_ctor_get(v_b_4707_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_b_4707_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4718_ = v_b_4707_;
v_isShared_4719_ = v_isSharedCheck_4760_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_snd_4715_);
lean_inc(v_fst_4716_);
lean_dec(v_b_4707_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4760_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v_array_4720_; lean_object* v_start_4721_; lean_object* v_stop_4722_; uint8_t v___x_4723_; 
v_array_4720_ = lean_ctor_get(v_snd_4715_, 0);
v_start_4721_ = lean_ctor_get(v_snd_4715_, 1);
v_stop_4722_ = lean_ctor_get(v_snd_4715_, 2);
v___x_4723_ = lean_nat_dec_lt(v_start_4721_, v_stop_4722_);
if (v___x_4723_ == 0)
{
lean_object* v___x_4725_; 
if (v_isShared_4719_ == 0)
{
v___x_4725_ = v___x_4718_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_fst_4716_);
lean_ctor_set(v_reuseFailAlloc_4727_, 1, v_snd_4715_);
v___x_4725_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
lean_object* v___x_4726_; 
v___x_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4725_);
return v___x_4726_;
}
}
else
{
lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4756_; 
lean_inc(v_stop_4722_);
lean_inc(v_start_4721_);
lean_inc_ref(v_array_4720_);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_snd_4715_);
if (v_isSharedCheck_4756_ == 0)
{
lean_object* v_unused_4757_; lean_object* v_unused_4758_; lean_object* v_unused_4759_; 
v_unused_4757_ = lean_ctor_get(v_snd_4715_, 2);
lean_dec(v_unused_4757_);
v_unused_4758_ = lean_ctor_get(v_snd_4715_, 1);
lean_dec(v_unused_4758_);
v_unused_4759_ = lean_ctor_get(v_snd_4715_, 0);
lean_dec(v_unused_4759_);
v___x_4729_ = v_snd_4715_;
v_isShared_4730_ = v_isSharedCheck_4756_;
goto v_resetjp_4728_;
}
else
{
lean_dec(v_snd_4715_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4756_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
lean_object* v_a_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4736_; 
v_a_4731_ = lean_array_uget_borrowed(v_as_4704_, v_i_4706_);
v___x_4732_ = lean_array_fget(v_array_4720_, v_start_4721_);
v___x_4733_ = lean_unsigned_to_nat(1u);
v___x_4734_ = lean_nat_add(v_start_4721_, v___x_4733_);
lean_dec(v_start_4721_);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 1, v___x_4734_);
v___x_4736_ = v___x_4729_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_array_4720_);
lean_ctor_set(v_reuseFailAlloc_4755_, 1, v___x_4734_);
lean_ctor_set(v_reuseFailAlloc_4755_, 2, v_stop_4722_);
v___x_4736_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
size_t v_sz_4737_; size_t v___x_4738_; lean_object* v___x_4739_; 
v_sz_4737_ = lean_array_size(v___x_4732_);
v___x_4738_ = ((size_t)0ULL);
lean_inc(v_a_4731_);
v___x_4739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4731_, v___x_4732_, v_sz_4737_, v___x_4738_, v_fst_4716_);
lean_dec(v___x_4732_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc(v_a_4740_);
lean_dec_ref_known(v___x_4739_, 1);
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 1, v___x_4736_);
lean_ctor_set(v___x_4718_, 0, v_a_4740_);
v___x_4742_ = v___x_4718_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_a_4740_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v___x_4736_);
v___x_4742_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
size_t v___x_4743_; size_t v___x_4744_; 
v___x_4743_ = ((size_t)1ULL);
v___x_4744_ = lean_usize_add(v_i_4706_, v___x_4743_);
v_i_4706_ = v___x_4744_;
v_b_4707_ = v___x_4742_;
goto _start;
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
lean_dec_ref(v___x_4736_);
lean_del_object(v___x_4718_);
v_a_4747_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4739_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4739_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2___boxed(lean_object* v_as_4761_, lean_object* v_sz_4762_, lean_object* v_i_4763_, lean_object* v_b_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
size_t v_sz_boxed_4770_; size_t v_i_boxed_4771_; lean_object* v_res_4772_; 
v_sz_boxed_4770_ = lean_unbox_usize(v_sz_4762_);
lean_dec(v_sz_4762_);
v_i_boxed_4771_ = lean_unbox_usize(v_i_4763_);
lean_dec(v_i_4763_);
v_res_4772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_as_4761_, v_sz_boxed_4770_, v_i_boxed_4771_, v_b_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec_ref(v_as_4761_);
return v_res_4772_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4774_; lean_object* v___x_4775_; 
v___x_4774_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4775_ = l_Lean_stringToMessageData(v___x_4774_);
return v___x_4775_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___f_4777_; 
v___x_4776_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4777_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1), 2, 1);
lean_closure_set(v___f_4777_, 0, v___x_4776_);
return v___f_4777_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4778_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4779_ = l_Lean_Expr_sort___override(v___x_4778_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4780_, lean_object* v_positions_4781_, lean_object* v_brecOnConst_4782_, lean_object* v_a_4783_, lean_object* v_a_4784_, lean_object* v_a_4785_, lean_object* v_a_4786_){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v_recArgInfo_4790_; lean_object* v_indicesPos_4791_; lean_object* v_indIdx_4792_; lean_object* v_numTypeFormers_4793_; lean_object* v___f_4794_; lean_object* v_brecOn_4795_; lean_object* v___f_4796_; uint8_t v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4788_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4789_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4790_ = lean_array_get_borrowed(v___x_4788_, v_recArgInfos_4780_, v___x_4789_);
v_indicesPos_4791_ = lean_ctor_get(v_recArgInfo_4790_, 3);
v_indIdx_4792_ = lean_ctor_get(v_recArgInfo_4790_, 5);
v_numTypeFormers_4793_ = lean_array_get_size(v_positions_4781_);
v___f_4794_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4794_, 0, v_numTypeFormers_4793_);
lean_inc(v_indIdx_4792_);
v_brecOn_4795_ = lean_apply_1(v_brecOnConst_4782_, v_indIdx_4792_);
v___f_4796_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4797_ = 0;
v___x_4798_ = lean_box(v___x_4797_);
lean_inc_ref(v_brecOn_4795_);
v___x_4799_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4799_, 0, v_brecOn_4795_);
lean_closure_set(v___x_4799_, 1, v___x_4798_);
v___x_4800_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4799_, v___f_4796_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v___x_4801_; 
lean_dec_ref_known(v___x_4800_, 1);
lean_inc(v_a_4786_);
lean_inc_ref(v_a_4785_);
lean_inc(v_a_4784_);
lean_inc_ref(v_a_4783_);
v___x_4801_ = lean_infer_type(v_brecOn_4795_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_object* v_a_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; uint8_t v___x_4807_; lean_object* v___x_4808_; 
v_a_4802_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_a_4802_);
lean_dec_ref_known(v___x_4801_, 1);
v___x_4803_ = lean_array_get_size(v_indicesPos_4791_);
v___x_4804_ = lean_unsigned_to_nat(1u);
v___x_4805_ = lean_nat_add(v___x_4803_, v___x_4804_);
v___x_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
v___x_4807_ = 0;
v___x_4808_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_a_4802_, v___x_4806_, v___f_4794_, v___x_4807_, v___x_4807_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; size_t v_sz_4815_; size_t v___x_4816_; lean_object* v___x_4817_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4809_);
lean_dec_ref_known(v___x_4808_, 1);
v___x_4810_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4781_);
v___x_4811_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4812_ = lean_mk_array(v___x_4810_, v___x_4811_);
v___x_4813_ = l_Array_toSubarray___redArg(v_positions_4781_, v___x_4789_, v_numTypeFormers_4793_);
v___x_4814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4812_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v_sz_4815_ = lean_array_size(v_a_4809_);
v___x_4816_ = ((size_t)0ULL);
v___x_4817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_a_4809_, v_sz_4815_, v___x_4816_, v___x_4814_, v_a_4783_, v_a_4784_, v_a_4785_, v_a_4786_);
lean_dec(v_a_4809_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4826_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4820_ = v___x_4817_;
v_isShared_4821_ = v_isSharedCheck_4826_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4817_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4826_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v_fst_4822_; lean_object* v___x_4824_; 
v_fst_4822_ = lean_ctor_get(v_a_4818_, 0);
lean_inc(v_fst_4822_);
lean_dec(v_a_4818_);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 0, v_fst_4822_);
v___x_4824_ = v___x_4820_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_fst_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
v_a_4827_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4817_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4817_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4781_);
return v___x_4808_;
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_dec_ref(v___f_4794_);
lean_dec_ref(v_positions_4781_);
v_a_4835_ = lean_ctor_get(v___x_4801_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4801_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4801_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4801_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4850_; 
lean_dec_ref(v_brecOn_4795_);
lean_dec_ref(v___f_4794_);
lean_dec_ref(v_positions_4781_);
v_a_4843_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4845_ = v___x_4800_;
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4800_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4848_; 
if (v_isShared_4846_ == 0)
{
v___x_4848_ = v___x_4845_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4843_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4851_, lean_object* v_positions_4852_, lean_object* v_brecOnConst_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_){
_start:
{
lean_object* v_res_4859_; 
v_res_4859_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4851_, v_positions_4852_, v_brecOnConst_4853_, v_a_4854_, v_a_4855_, v_a_4856_, v_a_4857_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
lean_dec(v_a_4855_);
lean_dec_ref(v_a_4854_);
lean_dec_ref(v_recArgInfos_4851_);
return v_res_4859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4860_, lean_object* v_as_4861_, size_t v_sz_4862_, size_t v_i_4863_, lean_object* v_b_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4860_, v_as_4861_, v_sz_4862_, v_i_4863_, v_b_4864_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4871_, lean_object* v_as_4872_, lean_object* v_sz_4873_, lean_object* v_i_4874_, lean_object* v_b_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_, lean_object* v___y_4880_){
_start:
{
size_t v_sz_boxed_4881_; size_t v_i_boxed_4882_; lean_object* v_res_4883_; 
v_sz_boxed_4881_ = lean_unbox_usize(v_sz_4873_);
lean_dec(v_sz_4873_);
v_i_boxed_4882_ = lean_unbox_usize(v_i_4874_);
lean_dec(v_i_4874_);
v_res_4883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4871_, v_as_4872_, v_sz_boxed_4881_, v_i_boxed_4882_, v_b_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
lean_dec(v___y_4879_);
lean_dec_ref(v___y_4878_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
lean_dec_ref(v_as_4872_);
return v_res_4883_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
if (lean_obj_tag(v_a_4884_) == 0)
{
lean_object* v___x_4886_; 
v___x_4886_ = l_List_reverse___redArg(v_a_4885_);
return v___x_4886_;
}
else
{
lean_object* v_head_4887_; lean_object* v_tail_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4899_; 
v_head_4887_ = lean_ctor_get(v_a_4884_, 0);
v_tail_4888_ = lean_ctor_get(v_a_4884_, 1);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_a_4884_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4890_ = v_a_4884_;
v_isShared_4891_ = v_isSharedCheck_4899_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_tail_4888_);
lean_inc(v_head_4887_);
lean_dec(v_a_4884_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4899_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4892_ = l_Nat_reprFast(v_head_4887_);
v___x_4893_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
v___x_4894_ = l_Lean_MessageData_ofFormat(v___x_4893_);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 1, v_a_4885_);
lean_ctor_set(v___x_4890_, 0, v___x_4894_);
v___x_4896_ = v___x_4890_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4898_, 1, v_a_4885_);
v___x_4896_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
v_a_4884_ = v_tail_4888_;
v_a_4885_ = v___x_4896_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_4900_, lean_object* v_a_4901_){
_start:
{
if (lean_obj_tag(v_a_4900_) == 0)
{
lean_object* v___x_4902_; 
v___x_4902_ = l_List_reverse___redArg(v_a_4901_);
return v___x_4902_;
}
else
{
lean_object* v_head_4903_; lean_object* v_tail_4904_; lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4916_; 
v_head_4903_ = lean_ctor_get(v_a_4900_, 0);
v_tail_4904_ = lean_ctor_get(v_a_4900_, 1);
v_isSharedCheck_4916_ = !lean_is_exclusive(v_a_4900_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4906_ = v_a_4900_;
v_isShared_4907_ = v_isSharedCheck_4916_;
goto v_resetjp_4905_;
}
else
{
lean_inc(v_tail_4904_);
lean_inc(v_head_4903_);
lean_dec(v_a_4900_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4916_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4913_; 
v___x_4908_ = lean_array_to_list(v_head_4903_);
v___x_4909_ = lean_box(0);
v___x_4910_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_4908_, v___x_4909_);
v___x_4911_ = l_Lean_MessageData_ofList(v___x_4910_);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 1, v_a_4901_);
lean_ctor_set(v___x_4906_, 0, v___x_4911_);
v___x_4913_ = v___x_4906_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4911_);
lean_ctor_set(v_reuseFailAlloc_4915_, 1, v_a_4901_);
v___x_4913_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
v_a_4900_ = v_tail_4904_;
v_a_4901_ = v___x_4913_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_4917_, lean_object* v_v_4918_, lean_object* v_i_4919_){
_start:
{
lean_object* v___x_4920_; uint8_t v___x_4921_; 
v___x_4920_ = lean_array_get_size(v_xs_4917_);
v___x_4921_ = lean_nat_dec_lt(v_i_4919_, v___x_4920_);
if (v___x_4921_ == 0)
{
lean_object* v___x_4922_; 
lean_dec(v_i_4919_);
v___x_4922_ = lean_box(0);
return v___x_4922_;
}
else
{
lean_object* v___x_4923_; uint8_t v___x_4924_; 
v___x_4923_ = lean_array_fget_borrowed(v_xs_4917_, v_i_4919_);
v___x_4924_ = lean_nat_dec_eq(v___x_4923_, v_v_4918_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; lean_object* v___x_4926_; 
v___x_4925_ = lean_unsigned_to_nat(1u);
v___x_4926_ = lean_nat_add(v_i_4919_, v___x_4925_);
lean_dec(v_i_4919_);
v_i_4919_ = v___x_4926_;
goto _start;
}
else
{
lean_object* v___x_4928_; 
v___x_4928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4928_, 0, v_i_4919_);
return v___x_4928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_4929_, lean_object* v_v_4930_, lean_object* v_i_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4929_, v_v_4930_, v_i_4931_);
lean_dec(v_v_4930_);
lean_dec_ref(v_xs_4929_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_4933_, lean_object* v_v_4934_){
_start:
{
lean_object* v___x_4935_; lean_object* v___x_4936_; 
v___x_4935_ = lean_unsigned_to_nat(0u);
v___x_4936_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_4933_, v_v_4934_, v___x_4935_);
return v___x_4936_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_4937_, lean_object* v_v_4938_){
_start:
{
lean_object* v_res_4939_; 
v_res_4939_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_4937_, v_v_4938_);
lean_dec(v_v_4938_);
lean_dec_ref(v_xs_4937_);
return v_res_4939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_4943_, lean_object* v_as_4944_, size_t v_sz_4945_, size_t v_i_4946_, lean_object* v_b_4947_){
_start:
{
uint8_t v___x_4948_; 
v___x_4948_ = lean_usize_dec_lt(v_i_4946_, v_sz_4945_);
if (v___x_4948_ == 0)
{
lean_inc_ref(v_b_4947_);
return v_b_4947_;
}
else
{
lean_object* v___x_4949_; lean_object* v_a_4950_; lean_object* v___x_4951_; 
v___x_4949_ = lean_box(0);
v_a_4950_ = lean_array_uget_borrowed(v_as_4944_, v_i_4946_);
v___x_4951_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_4950_, v_fnIdx_4943_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_object* v___x_4952_; size_t v___x_4953_; size_t v___x_4954_; 
v___x_4952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_4953_ = ((size_t)1ULL);
v___x_4954_ = lean_usize_add(v_i_4946_, v___x_4953_);
v_i_4946_ = v___x_4954_;
v_b_4947_ = v___x_4952_;
goto _start;
}
else
{
lean_object* v_val_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4967_; 
v_val_4956_ = lean_ctor_get(v___x_4951_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4951_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4958_ = v___x_4951_;
v_isShared_4959_ = v_isSharedCheck_4967_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_val_4956_);
lean_dec(v___x_4951_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4967_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4963_; 
v___x_4960_ = lean_array_get_size(v_a_4950_);
v___x_4961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4960_);
lean_ctor_set(v___x_4961_, 1, v_val_4956_);
if (v_isShared_4959_ == 0)
{
lean_ctor_set(v___x_4958_, 0, v___x_4961_);
v___x_4963_ = v___x_4958_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v___x_4961_);
v___x_4963_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4963_);
v___x_4965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4964_);
lean_ctor_set(v___x_4965_, 1, v___x_4949_);
return v___x_4965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_4968_, lean_object* v_as_4969_, lean_object* v_sz_4970_, lean_object* v_i_4971_, lean_object* v_b_4972_){
_start:
{
size_t v_sz_boxed_4973_; size_t v_i_boxed_4974_; lean_object* v_res_4975_; 
v_sz_boxed_4973_ = lean_unbox_usize(v_sz_4970_);
lean_dec(v_sz_4970_);
v_i_boxed_4974_ = lean_unbox_usize(v_i_4971_);
lean_dec(v_i_4971_);
v_res_4975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4968_, v_as_4969_, v_sz_boxed_4973_, v_i_boxed_4974_, v_b_4972_);
lean_dec_ref(v_b_4972_);
lean_dec_ref(v_as_4969_);
lean_dec(v_fnIdx_4968_);
return v_res_4975_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4977_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_4978_ = l_Lean_stringToMessageData(v___x_4977_);
return v___x_4978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_4979_, lean_object* v_positions_4980_, lean_object* v_fnIdx_4981_, lean_object* v_brecOnConst_4982_, lean_object* v_packedFArgs_4983_, lean_object* v_funTypes_4984_, lean_object* v_ys_4985_, lean_object* v___value_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v___x_5006_; lean_object* v_fst_5007_; lean_object* v_snd_5008_; lean_object* v___x_5009_; size_t v_sz_5010_; size_t v___x_5011_; lean_object* v___x_5012_; lean_object* v_fst_5013_; 
lean_inc_ref(v_ys_4985_);
lean_inc_ref(v_recArgInfo_4979_);
v___x_5006_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4979_, v_ys_4985_);
v_fst_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_fst_5007_);
v_snd_5008_ = lean_ctor_get(v___x_5006_, 1);
lean_inc(v_snd_5008_);
lean_dec_ref(v___x_5006_);
v___x_5009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5010_ = lean_array_size(v_positions_4980_);
v___x_5011_ = ((size_t)0ULL);
v___x_5012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_4981_, v_positions_4980_, v_sz_5010_, v___x_5011_, v___x_5009_);
v_fst_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_fst_5013_);
lean_dec_ref(v___x_5012_);
if (lean_obj_tag(v_fst_5013_) == 0)
{
lean_dec(v_snd_5008_);
lean_dec(v_fst_5007_);
lean_dec_ref(v_ys_4985_);
lean_dec_ref(v_brecOnConst_4982_);
lean_dec_ref(v_recArgInfo_4979_);
goto v___jp_4992_;
}
else
{
lean_object* v_val_5014_; 
v_val_5014_ = lean_ctor_get(v_fst_5013_, 0);
lean_inc(v_val_5014_);
lean_dec_ref_known(v_fst_5013_, 1);
if (lean_obj_tag(v_val_5014_) == 1)
{
lean_object* v_val_5015_; lean_object* v_fst_5016_; lean_object* v_snd_5017_; lean_object* v_indIdx_5018_; lean_object* v_brecOn_5019_; lean_object* v_brecOn_5020_; lean_object* v_brecOn_5021_; lean_object* v___x_5022_; 
lean_dec(v_fnIdx_4981_);
lean_dec_ref(v_positions_4980_);
v_val_5015_ = lean_ctor_get(v_val_5014_, 0);
lean_inc(v_val_5015_);
lean_dec_ref_known(v_val_5014_, 1);
v_fst_5016_ = lean_ctor_get(v_val_5015_, 0);
lean_inc(v_fst_5016_);
v_snd_5017_ = lean_ctor_get(v_val_5015_, 1);
lean_inc(v_snd_5017_);
lean_dec(v_val_5015_);
v_indIdx_5018_ = lean_ctor_get(v_recArgInfo_4979_, 5);
lean_inc(v_indIdx_5018_);
lean_dec_ref(v_recArgInfo_4979_);
v_brecOn_5019_ = lean_apply_1(v_brecOnConst_4982_, v_indIdx_5018_);
v_brecOn_5020_ = l_Lean_mkAppN(v_brecOn_5019_, v_fst_5007_);
lean_dec(v_fst_5007_);
v_brecOn_5021_ = l_Lean_mkAppN(v_brecOn_5020_, v_packedFArgs_4983_);
v___x_5022_ = l_Lean_Meta_PProdN_projM(v_fst_5016_, v_snd_5017_, v_brecOn_5021_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v_snd_5017_);
lean_dec(v_fst_5016_);
if (lean_obj_tag(v___x_5022_) == 0)
{
lean_object* v_a_5023_; lean_object* v___x_5024_; uint8_t v___x_5025_; uint8_t v___x_5026_; lean_object* v___x_5027_; 
v_a_5023_ = lean_ctor_get(v___x_5022_, 0);
lean_inc(v_a_5023_);
lean_dec_ref_known(v___x_5022_, 1);
v___x_5024_ = l_Lean_mkAppN(v_a_5023_, v_snd_5008_);
lean_dec(v_snd_5008_);
v___x_5025_ = 1;
v___x_5026_ = 1;
v___x_5027_ = l_Lean_Meta_mkLetFVars(v_funTypes_4984_, v___x_5024_, v___x_5025_, v___x_5025_, v___x_5026_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; uint8_t v___x_5029_; lean_object* v___x_5030_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref_known(v___x_5027_, 1);
v___x_5029_ = 0;
v___x_5030_ = l_Lean_Meta_mkLambdaFVars(v_ys_4985_, v_a_5028_, v___x_5029_, v___x_5025_, v___x_5029_, v___x_5025_, v___x_5026_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec_ref(v_ys_4985_);
return v___x_5030_;
}
else
{
lean_dec_ref(v_ys_4985_);
return v___x_5027_;
}
}
else
{
lean_dec(v_snd_5008_);
lean_dec_ref(v_ys_4985_);
return v___x_5022_;
}
}
else
{
lean_dec(v_val_5014_);
lean_dec(v_snd_5008_);
lean_dec(v_fst_5007_);
lean_dec_ref(v_ys_4985_);
lean_dec_ref(v_brecOnConst_4982_);
lean_dec_ref(v_recArgInfo_4979_);
goto v___jp_4992_;
}
}
v___jp_4992_:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_4993_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_4994_ = l_Nat_reprFast(v_fnIdx_4981_);
v___x_4995_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
v___x_4996_ = l_Lean_MessageData_ofFormat(v___x_4995_);
v___x_4997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4993_);
lean_ctor_set(v___x_4997_, 1, v___x_4996_);
v___x_4998_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_4999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4997_);
lean_ctor_set(v___x_4999_, 1, v___x_4998_);
v___x_5000_ = lean_array_to_list(v_positions_4980_);
v___x_5001_ = lean_box(0);
v___x_5002_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5000_, v___x_5001_);
v___x_5003_ = l_Lean_MessageData_ofList(v___x_5002_);
v___x_5004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5004_, 0, v___x_4999_);
lean_ctor_set(v___x_5004_, 1, v___x_5003_);
v___x_5005_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5004_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
return v___x_5005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5031_, lean_object* v_positions_5032_, lean_object* v_fnIdx_5033_, lean_object* v_brecOnConst_5034_, lean_object* v_packedFArgs_5035_, lean_object* v_funTypes_5036_, lean_object* v_ys_5037_, lean_object* v___value_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5031_, v_positions_5032_, v_fnIdx_5033_, v_brecOnConst_5034_, v_packedFArgs_5035_, v_funTypes_5036_, v_ys_5037_, v___value_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
lean_dec(v___y_5040_);
lean_dec_ref(v___y_5039_);
lean_dec_ref(v___value_5038_);
lean_dec_ref(v_funTypes_5036_);
lean_dec_ref(v_packedFArgs_5035_);
return v_res_5044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5045_, lean_object* v_fnIdx_5046_, lean_object* v_brecOnConst_5047_, lean_object* v_packedFArgs_5048_, lean_object* v_funTypes_5049_, lean_object* v_recArgInfo_5050_, lean_object* v_value_5051_, lean_object* v_a_5052_, lean_object* v_a_5053_, lean_object* v_a_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v___f_5057_; uint8_t v___x_5058_; lean_object* v___x_5059_; 
v___f_5057_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5057_, 0, v_recArgInfo_5050_);
lean_closure_set(v___f_5057_, 1, v_positions_5045_);
lean_closure_set(v___f_5057_, 2, v_fnIdx_5046_);
lean_closure_set(v___f_5057_, 3, v_brecOnConst_5047_);
lean_closure_set(v___f_5057_, 4, v_packedFArgs_5048_);
lean_closure_set(v___f_5057_, 5, v_funTypes_5049_);
v___x_5058_ = 0;
v___x_5059_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5051_, v___f_5057_, v___x_5058_, v_a_5052_, v_a_5053_, v_a_5054_, v_a_5055_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5060_, lean_object* v_fnIdx_5061_, lean_object* v_brecOnConst_5062_, lean_object* v_packedFArgs_5063_, lean_object* v_funTypes_5064_, lean_object* v_recArgInfo_5065_, lean_object* v_value_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v_res_5072_; 
v_res_5072_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5060_, v_fnIdx_5061_, v_brecOnConst_5062_, v_packedFArgs_5063_, v_funTypes_5064_, v_recArgInfo_5065_, v_value_5066_, v_a_5067_, v_a_5068_, v_a_5069_, v_a_5070_);
lean_dec(v_a_5070_);
lean_dec_ref(v_a_5069_);
lean_dec(v_a_5068_);
lean_dec_ref(v_a_5067_);
return v_res_5072_;
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
