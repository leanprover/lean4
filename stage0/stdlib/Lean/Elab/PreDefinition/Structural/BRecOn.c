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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(lean_object* v_msgData_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_){
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
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msgData_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0___boxed(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msgData_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
return v_res_26_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(lean_object* v_msg_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_ref_33_; lean_object* v___x_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_43_; 
v_ref_33_ = lean_ctor_get(v___y_30_, 2);
v___x_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_43_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_43_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_41_; 
lean_inc(v_ref_33_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v_ref_33_);
lean_ctor_set(v___x_39_, 1, v_a_35_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 1);
lean_ctor_set(v___x_37_, 0, v___x_39_);
v___x_41_ = v___x_37_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_27_ = stack[0].m_obj;
lean_object* v___y_28_ = stack[1].m_obj;
lean_object* v___y_29_ = stack[2].m_obj;
lean_object* v___y_30_ = stack[3].m_obj;
lean_object* v___y_31_ = stack[4].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg___boxed(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_51_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__0));
v___x_54_ = l_Lean_stringToMessageData(v___x_53_);
return v___x_54_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___closed__1);
v___x_61_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_60_, v_a_55_, v_a_56_, v_a_57_, v_a_58_);
return v___x_61_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_55_ = stack[0].m_obj;
lean_object* v_a_56_ = stack[1].m_obj;
lean_object* v_a_57_ = stack[2].m_obj;
lean_object* v_a_58_ = stack[3].m_obj;
lean_object* v_res_62_;
v_res_62_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_55_, v_a_56_, v_a_57_, v_a_58_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg___boxed(lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_63_, v_a_64_, v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_68_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(lean_object* v_00_u03b1_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_70_, v_a_71_, v_a_72_, v_a_73_);
return v___x_75_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_70_ = stack[1].m_obj;
lean_object* v_a_71_ = stack[2].m_obj;
lean_object* v_a_72_ = stack[3].m_obj;
lean_object* v_a_73_ = stack[4].m_obj;
lean_object* v_res_76_;
v_res_76_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(lean_box(0), v_a_70_, v_a_71_, v_a_72_, v_a_73_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___boxed(lean_object* v_00_u03b1_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed(v_00_u03b1_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_83_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(lean_object* v_00_u03b1_84_, lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
return v___x_91_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v_res_92_;
v_res_92_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(lean_box(0), v_msg_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___boxed(lean_object* v_00_u03b1_93_, lean_object* v_msg_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0(v_00_u03b1_93_, v_msg_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_100_;
}
}
lean_object* l_Lean_Elab_Structural_searchPProd___redArg(lean_object* v_e_109_, lean_object* v_F_110_, lean_object* v_k_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_117_; 
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc_ref(v_e_109_);
v___x_117_ = lean_whnf(v_e_109_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref_known(v___x_117_, 1);
switch(lean_obj_tag(v_a_118_))
{
case 5:
{
lean_object* v_fn_119_; 
v_fn_119_ = lean_ctor_get(v_a_118_, 0);
lean_inc_ref(v_fn_119_);
if (lean_obj_tag(v_fn_119_) == 5)
{
lean_object* v_fn_120_; 
v_fn_120_ = lean_ctor_get(v_fn_119_, 0);
if (lean_obj_tag(v_fn_120_) == 4)
{
lean_object* v_declName_121_; 
v_declName_121_ = lean_ctor_get(v_fn_120_, 0);
lean_inc(v_declName_121_);
if (lean_obj_tag(v_declName_121_) == 1)
{
lean_object* v_pre_122_; 
v_pre_122_ = lean_ctor_get(v_declName_121_, 0);
if (lean_obj_tag(v_pre_122_) == 0)
{
lean_object* v_arg_123_; lean_object* v_arg_124_; lean_object* v_str_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_123_ = lean_ctor_get(v_a_118_, 1);
lean_inc_ref(v_arg_123_);
lean_dec_ref_known(v_a_118_, 2);
v_arg_124_ = lean_ctor_get(v_fn_119_, 1);
lean_inc_ref(v_arg_124_);
lean_dec_ref_known(v_fn_119_, 2);
v_str_125_ = lean_ctor_get(v_declName_121_, 1);
lean_inc_ref(v_str_125_);
lean_dec_ref_known(v_declName_121_, 2);
v___x_126_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__0));
v___x_127_ = lean_string_dec_eq(v_str_125_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__1));
v___x_129_ = lean_string_dec_eq(v_str_125_, v___x_128_);
lean_dec_ref(v_str_125_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_arg_123_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_130_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref(v_e_109_);
v___x_131_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__2));
v___x_132_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_110_);
v___x_133_ = l_Lean_Expr_proj___override(v___x_131_, v___x_132_, v_F_110_);
v___x_134_ = l_Lean_Meta_saveState___redArg(v_a_113_, v_a_115_);
if (lean_obj_tag(v___x_134_) == 0)
{
lean_object* v_a_135_; lean_object* v___x_136_; 
v_a_135_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_a_135_);
lean_dec_ref_known(v___x_134_, 1);
lean_inc_ref(v_k_111_);
v___x_136_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_124_, v___x_133_, v_k_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_dec(v_a_135_);
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
return v___x_136_;
}
else
{
lean_object* v_a_137_; uint8_t v___y_139_; uint8_t v___x_152_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v___x_152_ = l_Lean_Exception_isInterrupt(v_a_137_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
lean_inc(v_a_137_);
v___x_153_ = l_Lean_Exception_isRuntime(v_a_137_);
v___y_139_ = v___x_153_;
goto v___jp_138_;
}
else
{
v___y_139_ = v___x_152_;
goto v___jp_138_;
}
v___jp_138_:
{
if (v___y_139_ == 0)
{
lean_object* v___x_140_; 
lean_dec_ref_known(v___x_136_, 1);
v___x_140_ = l_Lean_Meta_SavedState_restore___redArg(v_a_135_, v_a_113_, v_a_115_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec_ref_known(v___x_140_, 1);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = l_Lean_Expr_proj___override(v___x_131_, v___x_141_, v_F_110_);
v_e_109_ = v_arg_123_;
v_F_110_ = v___x_142_;
goto _start;
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
v_a_144_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_140_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_140_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_dec(v_a_135_);
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
return v___x_136_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v___x_133_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
v_a_154_ = lean_ctor_get(v___x_134_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_134_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_134_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_134_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec_ref(v_str_125_);
lean_dec_ref(v_e_109_);
v___x_162_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__3));
v___x_163_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_F_110_);
v___x_164_ = l_Lean_Expr_proj___override(v___x_162_, v___x_163_, v_F_110_);
v___x_165_ = l_Lean_Meta_saveState___redArg(v_a_113_, v_a_115_);
if (lean_obj_tag(v___x_165_) == 0)
{
lean_object* v_a_166_; lean_object* v___x_167_; 
v_a_166_ = lean_ctor_get(v___x_165_, 0);
lean_inc(v_a_166_);
lean_dec_ref_known(v___x_165_, 1);
lean_inc_ref(v_k_111_);
v___x_167_ = l_Lean_Elab_Structural_searchPProd___redArg(v_arg_124_, v___x_164_, v_k_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_dec(v_a_166_);
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
return v___x_167_;
}
else
{
lean_object* v_a_168_; uint8_t v___y_170_; uint8_t v___x_183_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v___x_183_ = l_Lean_Exception_isInterrupt(v_a_168_);
if (v___x_183_ == 0)
{
uint8_t v___x_184_; 
lean_inc(v_a_168_);
v___x_184_ = l_Lean_Exception_isRuntime(v_a_168_);
v___y_170_ = v___x_184_;
goto v___jp_169_;
}
else
{
v___y_170_ = v___x_183_;
goto v___jp_169_;
}
v___jp_169_:
{
if (v___y_170_ == 0)
{
lean_object* v___x_171_; 
lean_dec_ref_known(v___x_167_, 1);
v___x_171_ = l_Lean_Meta_SavedState_restore___redArg(v_a_166_, v_a_113_, v_a_115_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec_ref_known(v___x_171_, 1);
v___x_172_ = lean_unsigned_to_nat(1u);
v___x_173_ = l_Lean_Expr_proj___override(v___x_162_, v___x_172_, v_F_110_);
v_e_109_ = v_arg_123_;
v_F_110_ = v___x_173_;
goto _start;
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
v_a_175_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_171_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_171_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_dec(v_a_166_);
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v___x_164_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_arg_123_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
v_a_185_ = lean_ctor_get(v___x_165_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_165_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_165_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_165_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
else
{
lean_object* v___x_193_; 
lean_dec_ref_known(v_declName_121_, 2);
lean_dec_ref_known(v_fn_119_, 2);
lean_dec_ref_known(v_a_118_, 2);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_193_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_193_;
}
}
else
{
lean_object* v___x_194_; 
lean_dec(v_declName_121_);
lean_dec_ref_known(v_fn_119_, 2);
lean_dec_ref_known(v_a_118_, 2);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_194_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_194_;
}
}
else
{
lean_object* v___x_195_; 
lean_dec_ref_known(v_fn_119_, 2);
lean_dec_ref_known(v_a_118_, 2);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_195_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_195_;
}
}
else
{
lean_object* v___x_196_; 
lean_dec_ref_known(v_a_118_, 2);
lean_dec_ref(v_fn_119_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_196_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_196_;
}
}
case 4:
{
lean_object* v_declName_197_; 
v_declName_197_ = lean_ctor_get(v_a_118_, 0);
lean_inc(v_declName_197_);
lean_dec_ref_known(v_a_118_, 2);
if (lean_obj_tag(v_declName_197_) == 1)
{
lean_object* v_pre_198_; 
v_pre_198_ = lean_ctor_get(v_declName_197_, 0);
if (lean_obj_tag(v_pre_198_) == 0)
{
lean_object* v_str_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_str_199_ = lean_ctor_get(v_declName_197_, 1);
lean_inc_ref(v_str_199_);
lean_dec_ref_known(v_declName_197_, 2);
v___x_200_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__4));
v___x_201_ = lean_string_dec_eq(v_str_199_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_Elab_Structural_searchPProd___redArg___closed__5));
v___x_203_ = lean_string_dec_eq(v_str_199_, v___x_202_);
lean_dec_ref(v_str_199_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_204_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
lean_dec_ref(v_e_109_);
v___x_205_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_112_, v_a_113_, v_a_114_, v_a_115_);
return v___x_205_;
}
}
else
{
lean_object* v___x_206_; 
lean_dec_ref(v_str_199_);
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
lean_dec_ref(v_e_109_);
v___x_206_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v_a_112_, v_a_113_, v_a_114_, v_a_115_);
return v___x_206_;
}
}
else
{
lean_object* v___x_207_; 
lean_dec_ref_known(v_declName_197_, 2);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_207_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_207_;
}
}
else
{
lean_object* v___x_208_; 
lean_dec(v_declName_197_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_208_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_208_;
}
}
default: 
{
lean_object* v___x_209_; 
lean_dec(v_a_118_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
v___x_209_ = lean_apply_7(v_k_111_, v_e_109_, v_F_110_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, lean_box(0));
return v___x_209_;
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec_ref(v_k_111_);
lean_dec_ref(v_F_110_);
lean_dec_ref(v_e_109_);
v_a_210_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_117_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_117_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_searchPProd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_109_ = stack[0].m_obj;
lean_object* v_F_110_ = stack[1].m_obj;
lean_object* v_k_111_ = stack[2].m_obj;
lean_object* v_a_112_ = stack[3].m_obj;
lean_object* v_a_113_ = stack[4].m_obj;
lean_object* v_a_114_ = stack[5].m_obj;
lean_object* v_a_115_ = stack[6].m_obj;
lean_object* v_res_218_;
v_res_218_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_109_, v_F_110_, v_k_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___redArg___boxed(lean_object* v_e_219_, lean_object* v_F_220_, lean_object* v_k_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_219_, v_F_220_, v_k_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
return v_res_227_;
}
}
lean_object* l_Lean_Elab_Structural_searchPProd(lean_object* v_00_u03b1_228_, lean_object* v_e_229_, lean_object* v_F_230_, lean_object* v_k_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Elab_Structural_searchPProd___redArg(v_e_229_, v_F_230_, v_k_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
return v___x_237_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_searchPProd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_229_ = stack[1].m_obj;
lean_object* v_F_230_ = stack[2].m_obj;
lean_object* v_k_231_ = stack[3].m_obj;
lean_object* v_a_232_ = stack[4].m_obj;
lean_object* v_a_233_ = stack[5].m_obj;
lean_object* v_a_234_ = stack[6].m_obj;
lean_object* v_a_235_ = stack[7].m_obj;
lean_object* v_res_238_;
v_res_238_ = l_Lean_Elab_Structural_searchPProd(lean_box(0), v_e_229_, v_F_230_, v_k_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_searchPProd___boxed(lean_object* v_00_u03b1_239_, lean_object* v_e_240_, lean_object* v_F_241_, lean_object* v_k_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Elab_Structural_searchPProd(v_00_u03b1_239_, v_e_240_, v_F_241_, v_k_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
return v_res_248_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(lean_object* v_k_249_, lean_object* v_b_250_, lean_object* v_c_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; 
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
v___x_257_ = lean_apply_7(v_k_249_, v_b_250_, v_c_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, lean_box(0));
return v___x_257_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_249_ = stack[0].m_obj;
lean_object* v_b_250_ = stack[1].m_obj;
lean_object* v_c_251_ = stack[2].m_obj;
lean_object* v___y_252_ = stack[3].m_obj;
lean_object* v___y_253_ = stack[4].m_obj;
lean_object* v___y_254_ = stack[5].m_obj;
lean_object* v___y_255_ = stack[6].m_obj;
lean_object* v_res_258_;
v_res_258_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(v_k_249_, v_b_250_, v_c_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed(lean_object* v_k_259_, lean_object* v_b_260_, lean_object* v_c_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0(v_k_259_, v_b_260_, v_c_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(lean_object* v_type_268_, lean_object* v_k_269_, uint8_t v_cleanupAnnotations_270_, uint8_t v_whnfType_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___f_277_; lean_object* v___x_278_; 
v___f_277_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_277_, 0, v_k_269_);
v___x_278_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_268_, v___f_277_, v_cleanupAnnotations_270_, v_whnfType_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
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
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_278_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_278_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_268_ = stack[0].m_obj;
lean_object* v_k_269_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_270_ = stack[2].m_num;
uint8_t v_whnfType_271_ = stack[3].m_num;
lean_object* v___y_272_ = stack[4].m_obj;
lean_object* v___y_273_ = stack[5].m_obj;
lean_object* v___y_274_ = stack[6].m_obj;
lean_object* v___y_275_ = stack[7].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_268_, v_k_269_, v_cleanupAnnotations_270_, v_whnfType_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___boxed(lean_object* v_type_296_, lean_object* v_k_297_, lean_object* v_cleanupAnnotations_298_, lean_object* v_whnfType_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_305_; uint8_t v_whnfType_boxed_306_; lean_object* v_res_307_; 
v_cleanupAnnotations_boxed_305_ = lean_unbox(v_cleanupAnnotations_298_);
v_whnfType_boxed_306_ = lean_unbox(v_whnfType_299_);
v_res_307_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_296_, v_k_297_, v_cleanupAnnotations_boxed_305_, v_whnfType_boxed_306_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_307_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_object* v_00_u03b1_308_, lean_object* v_type_309_, lean_object* v_k_310_, uint8_t v_cleanupAnnotations_311_, uint8_t v_whnfType_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_type_309_, v_k_310_, v_cleanupAnnotations_311_, v_whnfType_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
return v___x_318_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_309_ = stack[1].m_obj;
lean_object* v_k_310_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_311_ = stack[3].m_num;
uint8_t v_whnfType_312_ = stack[4].m_num;
lean_object* v___y_313_ = stack[5].m_obj;
lean_object* v___y_314_ = stack[6].m_obj;
lean_object* v___y_315_ = stack[7].m_obj;
lean_object* v___y_316_ = stack[8].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(lean_box(0), v_type_309_, v_k_310_, v_cleanupAnnotations_311_, v_whnfType_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___boxed(lean_object* v_00_u03b1_320_, lean_object* v_type_321_, lean_object* v_k_322_, lean_object* v_cleanupAnnotations_323_, lean_object* v_whnfType_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_330_; uint8_t v_whnfType_boxed_331_; lean_object* v_res_332_; 
v_cleanupAnnotations_boxed_330_ = lean_unbox(v_cleanupAnnotations_323_);
v_whnfType_boxed_331_ = lean_unbox(v_whnfType_324_);
v_res_332_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1(v_00_u03b1_320_, v_type_321_, v_k_322_, v_cleanupAnnotations_boxed_330_, v_whnfType_boxed_331_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_332_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(lean_object* v_cls_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_toCold_342_; lean_object* v_options_343_; uint8_t v_hasTrace_344_; 
v_toCold_342_ = lean_ctor_get(v___y_339_, 0);
v_options_343_ = lean_ctor_get(v_toCold_342_, 2);
v_hasTrace_344_ = lean_ctor_get_uint8(v_options_343_, sizeof(void*)*1);
if (v_hasTrace_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_cls_336_);
v___x_345_ = lean_box(v_hasTrace_344_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
else
{
lean_object* v_inheritedTraceOptions_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_inheritedTraceOptions_347_ = lean_ctor_get(v_toCold_342_, 11);
v___x_348_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_349_ = l_Lean_Name_append(v___x_348_, v_cls_336_);
v___x_350_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_347_, v_options_343_, v___x_349_);
lean_dec(v___x_349_);
v___x_351_ = lean_box(v___x_350_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_336_ = stack[0].m_obj;
lean_object* v___y_337_ = stack[1].m_obj;
lean_object* v___y_338_ = stack[2].m_obj;
lean_object* v___y_339_ = stack[3].m_obj;
lean_object* v___y_340_ = stack[4].m_obj;
lean_object* v_res_353_;
v_res_353_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___boxed(lean_object* v_cls_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
return v_res_360_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0(void){
_start:
{
lean_object* v___x_361_; double v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_float_of_nat(v___x_361_);
return v___x_362_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(lean_object* v_cls_366_, lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_ref_373_; lean_object* v___x_374_; lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_420_; 
v_ref_373_ = lean_ctor_get(v___y_370_, 2);
v___x_374_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_420_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_420_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_420_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v_traceState_380_; lean_object* v_env_381_; lean_object* v_nextMacroScope_382_; lean_object* v_ngen_383_; lean_object* v_auxDeclNGen_384_; lean_object* v_cache_385_; lean_object* v_recordedDeps_386_; lean_object* v_messages_387_; lean_object* v_infoState_388_; lean_object* v_snapshotTasks_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_419_; 
v___x_379_ = lean_st_ref_take(v___y_371_);
v_traceState_380_ = lean_ctor_get(v___x_379_, 4);
v_env_381_ = lean_ctor_get(v___x_379_, 0);
v_nextMacroScope_382_ = lean_ctor_get(v___x_379_, 1);
v_ngen_383_ = lean_ctor_get(v___x_379_, 2);
v_auxDeclNGen_384_ = lean_ctor_get(v___x_379_, 3);
v_cache_385_ = lean_ctor_get(v___x_379_, 5);
v_recordedDeps_386_ = lean_ctor_get(v___x_379_, 6);
v_messages_387_ = lean_ctor_get(v___x_379_, 7);
v_infoState_388_ = lean_ctor_get(v___x_379_, 8);
v_snapshotTasks_389_ = lean_ctor_get(v___x_379_, 9);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_419_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_419_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_snapshotTasks_389_);
lean_inc(v_infoState_388_);
lean_inc(v_messages_387_);
lean_inc(v_recordedDeps_386_);
lean_inc(v_cache_385_);
lean_inc(v_traceState_380_);
lean_inc(v_auxDeclNGen_384_);
lean_inc(v_ngen_383_);
lean_inc(v_nextMacroScope_382_);
lean_inc(v_env_381_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_419_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint64_t v_tid_393_; lean_object* v_traces_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_418_; 
v_tid_393_ = lean_ctor_get_uint64(v_traceState_380_, sizeof(void*)*1);
v_traces_394_ = lean_ctor_get(v_traceState_380_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v_traceState_380_);
if (v_isSharedCheck_418_ == 0)
{
v___x_396_ = v_traceState_380_;
v_isShared_397_ = v_isSharedCheck_418_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_traces_394_);
lean_dec(v_traceState_380_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_418_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; double v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_398_ = lean_box(0);
v___x_399_ = lean_box(0);
v___x_400_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_401_ = 0;
v___x_402_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_403_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_403_, 0, v_cls_366_);
lean_ctor_set(v___x_403_, 1, v___x_399_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
lean_ctor_set_float(v___x_403_, sizeof(void*)*3, v___x_400_);
lean_ctor_set_float(v___x_403_, sizeof(void*)*3 + 8, v___x_400_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3 + 16, v___x_401_);
v___x_404_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_405_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v_a_375_);
lean_ctor_set(v___x_405_, 2, v___x_404_);
lean_inc(v_ref_373_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_ref_373_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_PersistentArray_push___redArg(v_traces_394_, v___x_406_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_407_);
v___x_409_ = v___x_396_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_407_);
lean_ctor_set_uint64(v_reuseFailAlloc_417_, sizeof(void*)*1, v_tid_393_);
v___x_409_ = v_reuseFailAlloc_417_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 4, v___x_409_);
v___x_411_ = v___x_391_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_env_381_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_nextMacroScope_382_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v_ngen_383_);
lean_ctor_set(v_reuseFailAlloc_416_, 3, v_auxDeclNGen_384_);
lean_ctor_set(v_reuseFailAlloc_416_, 4, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_416_, 5, v_cache_385_);
lean_ctor_set(v_reuseFailAlloc_416_, 6, v_recordedDeps_386_);
lean_ctor_set(v_reuseFailAlloc_416_, 7, v_messages_387_);
lean_ctor_set(v_reuseFailAlloc_416_, 8, v_infoState_388_);
lean_ctor_set(v_reuseFailAlloc_416_, 9, v_snapshotTasks_389_);
v___x_411_ = v_reuseFailAlloc_416_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = lean_st_ref_put(v___y_371_, v___x_411_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_398_);
v___x_414_ = v___x_377_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_398_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_366_ = stack[0].m_obj;
lean_object* v_msg_367_ = stack[1].m_obj;
lean_object* v___y_368_ = stack[2].m_obj;
lean_object* v___y_369_ = stack[3].m_obj;
lean_object* v___y_370_ = stack[4].m_obj;
lean_object* v___y_371_ = stack[5].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_366_, v_msg_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___boxed(lean_object* v_cls_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_422_, v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_429_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__0));
v___x_432_ = l_Lean_stringToMessageData(v___x_431_);
return v___x_432_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__2));
v___x_435_ = l_Lean_stringToMessageData(v___x_434_);
return v___x_435_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(lean_object* v_a_436_, lean_object* v_C_437_, lean_object* v_cls_438_, lean_object* v___f_439_, lean_object* v_belowDict_440_, lean_object* v_F_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___x_516_; 
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
v___x_516_ = lean_apply_5(v___f_439_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, lean_box(0));
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; uint8_t v___x_518_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = lean_unbox(v_a_517_);
lean_dec(v_a_517_);
if (v___x_518_ == 0)
{
goto v___jp_480_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_519_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__3);
lean_inc_ref(v_belowDict_440_);
v___x_520_ = l_Lean_indentExpr(v_belowDict_440_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
lean_inc(v_cls_438_);
v___x_522_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_438_, v___x_521_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_dec_ref_known(v___x_522_, 1);
goto v___jp_480_;
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_F_441_);
lean_dec_ref(v_belowDict_440_);
lean_dec(v_cls_438_);
lean_dec_ref(v_a_436_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v_F_441_);
lean_dec_ref(v_belowDict_440_);
lean_dec(v_cls_438_);
lean_dec_ref(v_a_436_);
v_a_531_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_516_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_516_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
v___jp_447_:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_isExprDefEq(v___y_448_, v_a_436_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_471_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_471_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_471_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint8_t v___x_458_; 
v___x_458_ = lean_unbox(v_a_454_);
lean_dec(v_a_454_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_467_; 
lean_del_object(v___x_456_);
lean_dec_ref(v_F_441_);
v___x_459_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_449_, v___y_450_, v___y_451_, v___y_452_);
v_a_460_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_467_ == 0)
{
v___x_462_ = v___x_459_;
v_isShared_463_ = v_isSharedCheck_467_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_459_);
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
else
{
lean_object* v___x_469_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v_F_441_);
v___x_469_ = v___x_456_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_F_441_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v_F_441_);
v_a_472_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_453_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_453_);
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
}
v___jp_480_:
{
if (lean_obj_tag(v_belowDict_440_) == 5)
{
lean_object* v_fn_481_; lean_object* v_arg_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
lean_dec(v_cls_438_);
v_fn_481_ = lean_ctor_get(v_belowDict_440_, 0);
lean_inc_ref(v_fn_481_);
v_arg_482_ = lean_ctor_get(v_belowDict_440_, 1);
lean_inc_ref(v_arg_482_);
lean_dec_ref_known(v_belowDict_440_, 2);
v___x_483_ = l_Lean_Expr_getAppFn(v_fn_481_);
lean_dec_ref(v_fn_481_);
v___x_484_ = lean_expr_eqv(v___x_483_, v_C_437_);
lean_dec_ref(v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v_arg_482_);
lean_dec_ref(v_F_441_);
lean_dec_ref(v_a_436_);
v___x_485_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_442_, v___y_443_, v___y_444_, v___y_445_);
v_a_486_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_485_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
v___y_448_ = v_arg_482_;
v___y_449_ = v___y_442_;
v___y_450_ = v___y_443_;
v___y_451_ = v___y_444_;
v___y_452_ = v___y_445_;
goto v___jp_447_;
}
}
else
{
lean_object* v_toCold_494_; lean_object* v_options_495_; uint8_t v_hasTrace_496_; 
lean_dec_ref(v_F_441_);
lean_dec_ref(v_a_436_);
v_toCold_494_ = lean_ctor_get(v___y_444_, 0);
v_options_495_ = lean_ctor_get(v_toCold_494_, 2);
v_hasTrace_496_ = lean_ctor_get_uint8(v_options_495_, sizeof(void*)*1);
if (v_hasTrace_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec_ref(v_belowDict_440_);
lean_dec(v_cls_438_);
v___x_497_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v___x_497_;
}
else
{
lean_object* v_inheritedTraceOptions_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_inheritedTraceOptions_498_ = lean_ctor_get(v_toCold_494_, 11);
v___x_499_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v_cls_438_);
v___x_500_ = l_Lean_Name_append(v___x_499_, v_cls_438_);
v___x_501_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_498_, v_options_495_, v___x_500_);
lean_dec(v___x_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
lean_dec_ref(v_belowDict_440_);
lean_dec(v_cls_438_);
v___x_502_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v___x_502_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___closed__1);
v___x_504_ = l_Lean_indentExpr(v_belowDict_440_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_438_, v___x_505_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_507_; 
lean_dec_ref_known(v___x_506_, 1);
v___x_507_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v___x_507_;
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_508_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_506_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_506_);
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
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_436_ = stack[0].m_obj;
lean_object* v_C_437_ = stack[1].m_obj;
lean_object* v_cls_438_ = stack[2].m_obj;
lean_object* v___f_439_ = stack[3].m_obj;
lean_object* v_belowDict_440_ = stack[4].m_obj;
lean_object* v_F_441_ = stack[5].m_obj;
lean_object* v___y_442_ = stack[6].m_obj;
lean_object* v___y_443_ = stack[7].m_obj;
lean_object* v___y_444_ = stack[8].m_obj;
lean_object* v___y_445_ = stack[9].m_obj;
lean_object* v_res_539_;
v_res_539_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v_a_436_, v_C_437_, v_cls_438_, v___f_439_, v_belowDict_440_, v_F_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed(lean_object* v_a_540_, lean_object* v_C_541_, lean_object* v_cls_542_, lean_object* v___f_543_, lean_object* v_belowDict_544_, lean_object* v_F_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1(v_a_540_, v_C_541_, v_cls_542_, v___f_543_, v_belowDict_544_, v_F_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec_ref(v_C_541_);
return v_res_551_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0(void){
_start:
{
lean_object* v___x_552_; lean_object* v_dummy_553_; 
v___x_552_ = lean_box(0);
v_dummy_553_ = l_Lean_Expr_sort___override(v___x_552_);
return v_dummy_553_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(lean_object* v_arg_554_, lean_object* v_C_555_, lean_object* v_cls_556_, lean_object* v___f_557_, lean_object* v_F_558_, lean_object* v_xs_559_, lean_object* v_belowDict_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v___x_566_; lean_object* v___x_567_; 
v___x_566_ = 1;
v___x_567_ = l_Lean_Meta_zetaReduce(v_arg_554_, v___x_566_, v___x_566_, v___x_566_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___f_569_; lean_object* v_dummy_570_; lean_object* v_nargs_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_n(v_a_568_, 2);
lean_dec_ref_known(v___x_567_, 1);
v___f_569_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__1___boxed), 11, 4);
lean_closure_set(v___f_569_, 0, v_a_568_);
lean_closure_set(v___f_569_, 1, v_C_555_);
lean_closure_set(v___f_569_, 2, v_cls_556_);
lean_closure_set(v___f_569_, 3, v___f_557_);
v_dummy_570_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_571_ = l_Lean_Expr_getAppNumArgs(v_a_568_);
lean_inc(v_nargs_571_);
v___x_572_ = lean_mk_array(v_nargs_571_, v_dummy_570_);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_sub(v_nargs_571_, v___x_573_);
lean_dec(v_nargs_571_);
v___x_575_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_568_, v___x_572_, v___x_574_);
v___x_588_ = lean_array_get_size(v_xs_559_);
v___x_589_ = lean_array_get_size(v___x_575_);
v___x_590_ = lean_nat_dec_le(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v___x_575_);
lean_dec_ref(v___f_569_);
lean_dec_ref(v_F_558_);
v___x_591_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_561_, v___y_562_, v___y_563_, v___y_564_);
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
v___y_577_ = v___y_561_;
v___y_578_ = v___y_562_;
v___y_579_ = v___y_563_;
v___y_580_ = v___y_564_;
goto v___jp_576_;
}
v___jp_576_:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_581_ = lean_array_get_size(v___x_575_);
v___x_582_ = lean_array_get_size(v_xs_559_);
v___x_583_ = lean_nat_sub(v___x_581_, v___x_582_);
v___x_584_ = l_Array_extract___redArg(v___x_575_, v___x_583_, v___x_581_);
lean_dec_ref(v___x_575_);
v___x_585_ = l_Lean_Expr_replaceFVars(v_belowDict_560_, v_xs_559_, v___x_584_);
v___x_586_ = l_Lean_mkAppN(v_F_558_, v___x_584_);
lean_dec_ref(v___x_584_);
v___x_587_ = l_Lean_Elab_Structural_searchPProd___redArg(v___x_585_, v___x_586_, v___f_569_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
return v___x_587_;
}
}
else
{
lean_dec_ref(v_F_558_);
lean_dec_ref(v___f_557_);
lean_dec(v_cls_556_);
lean_dec_ref(v_C_555_);
return v___x_567_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_554_ = stack[0].m_obj;
lean_object* v_C_555_ = stack[1].m_obj;
lean_object* v_cls_556_ = stack[2].m_obj;
lean_object* v___f_557_ = stack[3].m_obj;
lean_object* v_F_558_ = stack[4].m_obj;
lean_object* v_xs_559_ = stack[5].m_obj;
lean_object* v_belowDict_560_ = stack[6].m_obj;
lean_object* v___y_561_ = stack[7].m_obj;
lean_object* v___y_562_ = stack[8].m_obj;
lean_object* v___y_563_ = stack[9].m_obj;
lean_object* v___y_564_ = stack[10].m_obj;
lean_object* v_res_600_;
v_res_600_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_554_, v_C_555_, v_cls_556_, v___f_557_, v_F_558_, v_xs_559_, v_belowDict_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed(lean_object* v_arg_601_, lean_object* v_C_602_, lean_object* v_cls_603_, lean_object* v___f_604_, lean_object* v_F_605_, lean_object* v_xs_606_, lean_object* v_belowDict_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2(v_arg_601_, v_C_602_, v_cls_603_, v___f_604_, v_F_605_, v_xs_606_, v_belowDict_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec_ref(v_belowDict_607_);
lean_dec_ref(v_xs_606_);
return v_res_613_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__0));
v___x_616_ = l_Lean_stringToMessageData(v___x_615_);
return v___x_616_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(lean_object* v_arg_617_, lean_object* v_C_618_, lean_object* v_cls_619_, lean_object* v___f_620_, lean_object* v_belowDict_621_, lean_object* v_F_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___f_628_; lean_object* v___x_632_; 
lean_inc_ref(v___f_620_);
lean_inc(v_cls_619_);
v___f_628_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___boxed), 12, 5);
lean_closure_set(v___f_628_, 0, v_arg_617_);
lean_closure_set(v___f_628_, 1, v_C_618_);
lean_closure_set(v___f_628_, 2, v_cls_619_);
lean_closure_set(v___f_628_, 3, v___f_620_);
lean_closure_set(v___f_628_, 4, v_F_622_);
lean_inc(v___y_626_);
lean_inc_ref(v___y_625_);
lean_inc(v___y_624_);
lean_inc_ref(v___y_623_);
v___x_632_ = lean_apply_5(v___f_620_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, lean_box(0));
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; uint8_t v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_unbox(v_a_633_);
lean_dec(v_a_633_);
if (v___x_634_ == 0)
{
lean_dec(v_cls_619_);
goto v___jp_629_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___closed__1);
lean_inc_ref(v_belowDict_621_);
v___x_636_ = l_Lean_indentExpr(v_belowDict_621_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_619_, v___x_637_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_dec_ref_known(v___x_638_, 1);
goto v___jp_629_;
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v___f_628_);
lean_dec_ref(v_belowDict_621_);
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v___f_628_);
lean_dec_ref(v_belowDict_621_);
lean_dec(v_cls_619_);
v_a_647_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_632_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_632_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
v___jp_629_:
{
uint8_t v___x_630_; lean_object* v___x_631_; 
v___x_630_ = 0;
v___x_631_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg(v_belowDict_621_, v___f_628_, v___x_630_, v___x_630_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_631_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_617_ = stack[0].m_obj;
lean_object* v_C_618_ = stack[1].m_obj;
lean_object* v_cls_619_ = stack[2].m_obj;
lean_object* v___f_620_ = stack[3].m_obj;
lean_object* v_belowDict_621_ = stack[4].m_obj;
lean_object* v_F_622_ = stack[5].m_obj;
lean_object* v___y_623_ = stack[6].m_obj;
lean_object* v___y_624_ = stack[7].m_obj;
lean_object* v___y_625_ = stack[8].m_obj;
lean_object* v___y_626_ = stack[9].m_obj;
lean_object* v_res_655_;
v_res_655_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v_arg_617_, v_C_618_, v_cls_619_, v___f_620_, v_belowDict_621_, v_F_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed(lean_object* v_arg_656_, lean_object* v_C_657_, lean_object* v_cls_658_, lean_object* v___f_659_, lean_object* v_belowDict_660_, lean_object* v_F_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3(v_arg_656_, v_C_657_, v_cls_658_, v___f_659_, v_belowDict_660_, v_F_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_667_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__5));
v___x_679_ = l_Lean_stringToMessageData(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__7));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(lean_object* v_C_683_, lean_object* v_belowDict_684_, lean_object* v_arg_685_, lean_object* v_F_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_cls_692_; lean_object* v___f_693_; lean_object* v___f_694_; lean_object* v___x_695_; lean_object* v_a_696_; uint8_t v___x_697_; 
v_cls_692_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_693_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__4));
lean_inc_ref(v_arg_685_);
v___f_694_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__3___boxed), 11, 4);
lean_closure_set(v___f_694_, 0, v_arg_685_);
lean_closure_set(v___f_694_, 1, v_C_683_);
lean_closure_set(v___f_694_, 2, v_cls_692_);
lean_closure_set(v___f_694_, 3, v___f_693_);
v___x_695_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0(v_cls_692_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
v___x_697_ = lean_unbox(v_a_696_);
lean_dec(v_a_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_dec_ref(v_arg_685_);
v___x_698_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_684_, v_F_686_, v___f_694_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_699_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__6);
lean_inc_ref(v_belowDict_684_);
v___x_700_ = l_Lean_indentExpr(v_belowDict_684_);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__8);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_Lean_indentExpr(v_arg_685_);
v___x_705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0(v_cls_692_, v___x_705_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v___x_707_; 
lean_dec_ref_known(v___x_706_, 1);
v___x_707_ = l_Lean_Elab_Structural_searchPProd___redArg(v_belowDict_684_, v_F_686_, v___f_694_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
return v___x_707_;
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v___f_694_);
lean_dec_ref(v_F_686_);
lean_dec_ref(v_belowDict_684_);
v_a_708_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_706_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_706_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_C_683_ = stack[0].m_obj;
lean_object* v_belowDict_684_ = stack[1].m_obj;
lean_object* v_arg_685_ = stack[2].m_obj;
lean_object* v_F_686_ = stack[3].m_obj;
lean_object* v_a_687_ = stack[4].m_obj;
lean_object* v_a_688_ = stack[5].m_obj;
lean_object* v_a_689_ = stack[6].m_obj;
lean_object* v_a_690_ = stack[7].m_obj;
lean_object* v_res_716_;
v_res_716_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_683_, v_belowDict_684_, v_arg_685_, v_F_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
stack->m_obj
 = v_res_716_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___boxed(lean_object* v_C_717_, lean_object* v_belowDict_718_, lean_object* v_arg_719_, lean_object* v_F_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v_C_717_, v_belowDict_718_, v_arg_719_, v_F_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
return v_res_726_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(lean_object* v_t_727_, lean_object* v_x_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v_t_727_);
return v___x_734_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_727_ = stack[0].m_obj;
lean_object* v_x_728_ = stack[1].m_obj;
lean_object* v___y_729_ = stack[2].m_obj;
lean_object* v___y_730_ = stack[3].m_obj;
lean_object* v___y_731_ = stack[4].m_obj;
lean_object* v___y_732_ = stack[5].m_obj;
lean_object* v_res_735_;
v_res_735_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v_t_727_, v_x_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed(lean_object* v_t_736_, lean_object* v_x_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0(v_t_736_, v_x_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec_ref(v_x_737_);
return v_res_743_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(lean_object* v_t_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v___f_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___f_753_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_753_, 0, v_t_747_);
v___x_754_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___closed__1));
v___x_755_ = l_Lean_Core_mkFreshUserName(v___x_754_, v___y_750_, v___y_751_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_764_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_a_756_);
lean_ctor_set(v___x_760_, 1, v___f_753_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v___f_753_);
v_a_765_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_755_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_755_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_747_ = stack[0].m_obj;
lean_object* v___y_748_ = stack[1].m_obj;
lean_object* v___y_749_ = stack[2].m_obj;
lean_object* v___y_750_ = stack[3].m_obj;
lean_object* v___y_751_ = stack[4].m_obj;
lean_object* v_res_773_;
v_res_773_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
stack->m_obj
 = v_res_773_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1___boxed(lean_object* v_t_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__1(v_t_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_780_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(lean_object* v___x_781_, lean_object* v_a_782_, lean_object* v_x_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_array_set(v___y_784_, v_a_782_, v___x_781_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_781_ = stack[0].m_obj;
lean_object* v_a_782_ = stack[1].m_obj;
lean_object* v___y_784_ = stack[3].m_obj;
lean_object* v___y_785_ = stack[4].m_obj;
lean_object* v___y_786_ = stack[5].m_obj;
lean_object* v___y_787_ = stack[6].m_obj;
lean_object* v___y_788_ = stack[7].m_obj;
lean_object* v_res_793_;
v_res_793_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v___x_781_, v_a_782_, lean_box(0), v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed(lean_object* v___x_794_, lean_object* v_a_795_, lean_object* v_x_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2(v___x_794_, v_a_795_, v_x_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v_a_795_);
return v_res_803_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(lean_object* v___x_804_, lean_object* v_a_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_snd_813_; lean_object* v_fst_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_865_; 
v_snd_813_ = lean_ctor_get(v___y_807_, 1);
v_fst_814_ = lean_ctor_get(v___y_807_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___y_807_);
if (v_isSharedCheck_865_ == 0)
{
v___x_816_ = v___y_807_;
v_isShared_817_ = v_isSharedCheck_865_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_snd_813_);
lean_inc(v_fst_814_);
lean_dec(v___y_807_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_865_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_array_818_; lean_object* v_start_819_; lean_object* v_stop_820_; uint8_t v___x_821_; 
v_array_818_ = lean_ctor_get(v_snd_813_, 0);
v_start_819_ = lean_ctor_get(v_snd_813_, 1);
v_stop_820_ = lean_ctor_get(v_snd_813_, 2);
v___x_821_ = lean_nat_dec_lt(v_start_819_, v_stop_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref(v_a_805_);
lean_dec_ref(v___x_804_);
if (v_isShared_817_ == 0)
{
v___x_823_ = v___x_816_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_fst_814_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_snd_813_);
v___x_823_ = v_reuseFailAlloc_826_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
return v___x_825_;
}
}
else
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_861_; 
lean_inc(v_stop_820_);
lean_inc(v_start_819_);
lean_inc_ref(v_array_818_);
v_isSharedCheck_861_ = !lean_is_exclusive(v_snd_813_);
if (v_isSharedCheck_861_ == 0)
{
lean_object* v_unused_862_; lean_object* v_unused_863_; lean_object* v_unused_864_; 
v_unused_862_ = lean_ctor_get(v_snd_813_, 2);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_snd_813_, 1);
lean_dec(v_unused_863_);
v_unused_864_ = lean_ctor_get(v_snd_813_, 0);
lean_dec(v_unused_864_);
v___x_828_ = v_snd_813_;
v_isShared_829_ = v_isSharedCheck_861_;
goto v_resetjp_827_;
}
else
{
lean_dec(v_snd_813_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_861_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___f_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_830_ = lean_array_fget_borrowed(v_array_818_, v_start_819_);
lean_inc(v___x_830_);
v___f_831_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_831_, 0, v___x_830_);
v___x_832_ = lean_unsigned_to_nat(1u);
v___x_833_ = lean_nat_add(v_start_819_, v___x_832_);
lean_dec(v_start_819_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 1, v___x_833_);
v___x_835_ = v___x_828_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_array_818_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_stop_820_);
v___x_835_ = v_reuseFailAlloc_860_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
size_t v_sz_836_; size_t v___x_837_; lean_object* v___x_9002__overap_838_; lean_object* v___x_839_; 
v_sz_836_ = lean_array_size(v_a_805_);
v___x_837_ = ((size_t)0ULL);
v___x_9002__overap_838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_804_, v_a_805_, v___f_831_, v_sz_836_, v___x_837_, v_fst_814_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v___y_808_);
v___x_839_ = lean_apply_5(v___x_9002__overap_838_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, lean_box(0));
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_851_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_851_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_851_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_835_);
lean_ctor_set(v___x_816_, 0, v_a_840_);
v___x_845_ = v___x_816_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_840_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_835_);
v___x_845_ = v_reuseFailAlloc_850_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_846_);
v___x_848_ = v___x_842_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___x_835_);
lean_del_object(v___x_816_);
v_a_852_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_839_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_839_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
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
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_804_ = stack[0].m_obj;
lean_object* v_a_805_ = stack[1].m_obj;
lean_object* v___y_807_ = stack[3].m_obj;
lean_object* v___y_808_ = stack[4].m_obj;
lean_object* v___y_809_ = stack[5].m_obj;
lean_object* v___y_810_ = stack[6].m_obj;
lean_object* v___y_811_ = stack[7].m_obj;
lean_object* v_res_866_;
v_res_866_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_804_, v_a_805_, lean_box(0), v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed(lean_object* v___x_867_, lean_object* v_a_868_, lean_object* v_x_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3(v___x_867_, v_a_868_, v_x_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_876_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(lean_object* v___x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_toCold_883_; lean_object* v_options_884_; uint8_t v_hasTrace_885_; 
v_toCold_883_ = lean_ctor_get(v___y_880_, 0);
v_options_884_ = lean_ctor_get(v_toCold_883_, 2);
v_hasTrace_885_ = lean_ctor_get_uint8(v_options_884_, sizeof(void*)*1);
if (v_hasTrace_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v___x_877_);
v___x_886_ = lean_box(v_hasTrace_885_);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
else
{
lean_object* v_inheritedTraceOptions_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_inheritedTraceOptions_888_ = lean_ctor_get(v_toCold_883_, 11);
v___x_889_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_890_ = l_Lean_Name_append(v___x_889_, v___x_877_);
v___x_891_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_888_, v_options_884_, v___x_890_);
lean_dec(v___x_890_);
v___x_892_ = lean_box(v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_877_ = stack[0].m_obj;
lean_object* v___y_878_ = stack[1].m_obj;
lean_object* v___y_879_ = stack[2].m_obj;
lean_object* v___y_880_ = stack[3].m_obj;
lean_object* v___y_881_ = stack[4].m_obj;
lean_object* v_res_894_;
v_res_894_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
stack->m_obj
 = v_res_894_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4___boxed(lean_object* v___x_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
return v_res_901_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__1));
v___x_905_ = l_Lean_stringToMessageData(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__3));
v___x_908_ = l_Lean_stringToMessageData(v___x_907_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__6));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_positions_915_, lean_object* v_a_916_, lean_object* v___x_917_, lean_object* v___x_918_, lean_object* v_k_919_, lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v_toMonadRef_922_, lean_object* v___x_923_, lean_object* v___f_924_, lean_object* v_Cs_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; lean_object* v___x_9038__overap_932_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
lean_inc_ref(v_Cs_925_);
lean_inc_ref(v___x_913_);
v___x_9038__overap_932_ = l_Lean_Elab_Structural_Positions_mapMwith___redArg(v___x_913_, v___x_914_, v___x_931_, v_positions_915_, v_a_916_, v_Cs_925_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
v___x_933_ = lean_apply_5(v___x_9038__overap_932_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, lean_box(0));
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___x_977_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = l_Lean_mkAppN(v___x_917_, v_a_934_);
lean_dec(v_a_934_);
v___x_936_ = l_Subarray_copy___redArg(v___x_918_);
v___x_937_ = l_Lean_mkAppN(v___x_935_, v___x_936_);
lean_dec_ref(v___x_936_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
v___x_977_ = lean_apply_5(v___f_924_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, lean_box(0));
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; uint8_t v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_unbox(v_a_978_);
lean_dec(v_a_978_);
if (v___x_979_ == 0)
{
v___y_939_ = v___y_926_;
v___y_940_ = v___y_927_;
v___y_941_ = v___y_928_;
v___y_942_ = v___y_929_;
goto v___jp_938_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_9089__overap_991_; lean_object* v___x_992_; 
v___x_980_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__4);
lean_inc_ref(v_Cs_925_);
v___x_981_ = lean_array_to_list(v_Cs_925_);
v___x_982_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__5));
v___x_983_ = lean_box(0);
v___x_984_ = l_List_mapTR_loop___redArg(v___x_982_, v___x_981_, v___x_983_);
v___x_985_ = l_Lean_MessageData_ofList(v___x_984_);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_980_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__7);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
lean_inc_ref(v___x_937_);
v___x_989_ = l_Lean_indentExpr(v___x_937_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_inc(v___x_920_);
lean_inc_ref(v___x_923_);
lean_inc_ref(v_toMonadRef_922_);
lean_inc_ref(v___x_921_);
lean_inc_ref(v___x_913_);
v___x_9089__overap_991_ = l_Lean_addTrace___redArg(v___x_913_, v___x_921_, v_toMonadRef_922_, v___x_923_, v___x_920_, v___x_990_);
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
v___x_992_ = lean_apply_5(v___x_9089__overap_991_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, lean_box(0));
if (lean_obj_tag(v___x_992_) == 0)
{
lean_dec_ref_known(v___x_992_, 1);
v___y_939_ = v___y_926_;
v___y_940_ = v___y_927_;
v___y_941_ = v___y_928_;
v___y_942_ = v___y_929_;
goto v___jp_938_;
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v___x_937_);
lean_dec_ref(v_Cs_925_);
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v___x_913_);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v___x_937_);
lean_dec_ref(v_Cs_925_);
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v___x_913_);
v_a_1001_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_977_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_977_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
v___jp_938_:
{
lean_object* v_toCold_943_; lean_object* v_options_944_; uint8_t v_hasTrace_945_; 
v_toCold_943_ = lean_ctor_get(v___y_941_, 0);
v_options_944_ = lean_ctor_get(v_toCold_943_, 2);
v_hasTrace_945_ = lean_ctor_get_uint8(v_options_944_, sizeof(void*)*1);
if (v_hasTrace_945_ == 0)
{
lean_object* v___x_946_; 
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v___x_913_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
v___x_946_ = lean_apply_7(v_k_919_, v_Cs_925_, v___x_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, lean_box(0));
return v___x_946_;
}
else
{
lean_object* v_inheritedTraceOptions_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_inheritedTraceOptions_947_ = lean_ctor_get(v_toCold_943_, 11);
v___x_948_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_920_);
v___x_949_ = l_Lean_Name_append(v___x_948_, v___x_920_);
v___x_950_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_947_, v_options_944_, v___x_949_);
lean_dec(v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v___x_913_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
v___x_951_ = lean_apply_7(v_k_919_, v_Cs_925_, v___x_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, lean_box(0));
return v___x_951_;
}
else
{
lean_object* v___x_952_; 
lean_inc_ref(v___x_937_);
v___x_952_ = l_Lean_Meta_isTypeCorrect(v___x_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
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
if (v___x_950_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v___x_913_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
v___x_955_ = lean_apply_7(v_k_919_, v_Cs_925_, v___x_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, lean_box(0));
return v___x_955_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_9062__overap_957_; lean_object* v___x_958_; 
v___x_956_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
v___x_9062__overap_957_ = l_Lean_addTrace___redArg(v___x_913_, v___x_921_, v_toMonadRef_922_, v___x_923_, v___x_920_, v___x_956_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
v___x_958_ = lean_apply_5(v___x_9062__overap_957_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, lean_box(0));
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; 
lean_dec_ref_known(v___x_958_, 1);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
v___x_959_ = lean_apply_7(v_k_919_, v_Cs_925_, v___x_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, lean_box(0));
return v___x_959_;
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec_ref(v___x_937_);
lean_dec_ref(v_Cs_925_);
lean_dec_ref(v_k_919_);
v_a_960_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_958_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_958_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
else
{
lean_object* v___x_968_; 
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v___x_913_);
lean_inc(v___y_942_);
lean_inc_ref(v___y_941_);
lean_inc(v___y_940_);
lean_inc_ref(v___y_939_);
v___x_968_ = lean_apply_7(v_k_919_, v_Cs_925_, v___x_937_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, lean_box(0));
return v___x_968_;
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v___x_937_);
lean_dec_ref(v_Cs_925_);
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v___x_913_);
v_a_969_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_952_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_952_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_Cs_925_);
lean_dec_ref(v___f_924_);
lean_dec_ref(v___x_923_);
lean_dec_ref(v_toMonadRef_922_);
lean_dec_ref(v___x_921_);
lean_dec(v___x_920_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v___x_918_);
lean_dec_ref(v___x_917_);
lean_dec_ref(v___x_913_);
v_a_1009_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_933_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_933_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_913_ = stack[0].m_obj;
lean_object* v___x_914_ = stack[1].m_obj;
lean_object* v_positions_915_ = stack[2].m_obj;
lean_object* v_a_916_ = stack[3].m_obj;
lean_object* v___x_917_ = stack[4].m_obj;
lean_object* v___x_918_ = stack[5].m_obj;
lean_object* v_k_919_ = stack[6].m_obj;
lean_object* v___x_920_ = stack[7].m_obj;
lean_object* v___x_921_ = stack[8].m_obj;
lean_object* v_toMonadRef_922_ = stack[9].m_obj;
lean_object* v___x_923_ = stack[10].m_obj;
lean_object* v___f_924_ = stack[11].m_obj;
lean_object* v_Cs_925_ = stack[12].m_obj;
lean_object* v___y_926_ = stack[13].m_obj;
lean_object* v___y_927_ = stack[14].m_obj;
lean_object* v___y_928_ = stack[15].m_obj;
lean_object* v___y_929_ = stack[16].m_obj;
lean_object* v_res_1017_;
v_res_1017_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_913_, v___x_914_, v_positions_915_, v_a_916_, v___x_917_, v___x_918_, v_k_919_, v___x_920_, v___x_921_, v_toMonadRef_922_, v___x_923_, v___f_924_, v_Cs_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
stack->m_obj
 = v_res_1017_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_1018_ = _args[0];
lean_object* v___x_1019_ = _args[1];
lean_object* v_positions_1020_ = _args[2];
lean_object* v_a_1021_ = _args[3];
lean_object* v___x_1022_ = _args[4];
lean_object* v___x_1023_ = _args[5];
lean_object* v_k_1024_ = _args[6];
lean_object* v___x_1025_ = _args[7];
lean_object* v___x_1026_ = _args[8];
lean_object* v_toMonadRef_1027_ = _args[9];
lean_object* v___x_1028_ = _args[10];
lean_object* v___f_1029_ = _args[11];
lean_object* v_Cs_1030_ = _args[12];
lean_object* v___y_1031_ = _args[13];
lean_object* v___y_1032_ = _args[14];
lean_object* v___y_1033_ = _args[15];
lean_object* v___y_1034_ = _args[16];
lean_object* v___y_1035_ = _args[17];
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5(v___x_1018_, v___x_1019_, v_positions_1020_, v_a_1021_, v___x_1022_, v___x_1023_, v_k_1024_, v___x_1025_, v___x_1026_, v_toMonadRef_1027_, v___x_1028_, v___f_1029_, v_Cs_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_unsigned_to_nat(37u);
v___x_1038_ = l_Lean_Level_ofNat(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__0);
v___x_1040_ = l_Lean_Expr_sort___override(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__2));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__4));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(lean_object* v_positions_1047_, lean_object* v___x_1048_, lean_object* v___f_1049_, lean_object* v___f_1050_, lean_object* v___x_1051_, lean_object* v_numTypeFormers_1052_, lean_object* v___x_1053_, lean_object* v_k_1054_, lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v_toMonadRef_1057_, lean_object* v___x_1058_, lean_object* v___f_1059_, lean_object* v_numIndParams_1060_, lean_object* v_a_1061_, lean_object* v_f_1062_, lean_object* v_args_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v_lower_1119_; lean_object* v_upper_1120_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; 
v___x_1186_ = lean_nat_add(v_numIndParams_1060_, v_numTypeFormers_1052_);
v___x_1187_ = lean_array_get_size(v_args_1063_);
v___x_1188_ = lean_nat_dec_lt(v___x_1186_, v___x_1187_);
lean_dec(v___x_1186_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
lean_dec_ref(v_args_1063_);
lean_dec_ref(v_f_1062_);
lean_dec(v_numIndParams_1060_);
lean_dec_ref(v_k_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v_numTypeFormers_1052_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v_positions_1047_);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
v___x_1189_ = lean_apply_5(v___f_1059_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, lean_box(0));
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; uint8_t v___x_1191_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v___x_1189_, 1);
v___x_1191_ = lean_unbox(v_a_1190_);
lean_dec(v_a_1190_);
if (v___x_1191_ == 0)
{
lean_dec_ref(v_a_1061_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_toMonadRef_1057_);
lean_dec_ref(v___x_1056_);
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1048_);
v___y_1173_ = v___y_1064_;
v___y_1174_ = v___y_1065_;
v___y_1175_ = v___y_1066_;
v___y_1176_ = v___y_1067_;
goto v___jp_1172_;
}
else
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_9218__overap_1195_; lean_object* v___x_1196_; 
v___x_1192_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__5);
v___x_1193_ = l_Lean_indentExpr(v_a_1061_);
v___x_1194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_9218__overap_1195_ = l_Lean_addTrace___redArg(v___x_1048_, v___x_1056_, v_toMonadRef_1057_, v___x_1058_, v___x_1055_, v___x_1194_);
lean_inc(v___y_1067_);
lean_inc_ref(v___y_1066_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
v___x_1196_ = lean_apply_5(v___x_9218__overap_1195_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, lean_box(0));
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_dec_ref_known(v___x_1196_, 1);
v___y_1173_ = v___y_1064_;
v___y_1174_ = v___y_1065_;
v___y_1175_ = v___y_1066_;
v___y_1176_ = v___y_1067_;
goto v___jp_1172_;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec_ref(v_a_1061_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_toMonadRef_1057_);
lean_dec_ref(v___x_1056_);
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1048_);
v_a_1205_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1189_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1189_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_dec_ref(v_a_1061_);
v___y_1163_ = v___y_1064_;
v___y_1164_ = v___y_1065_;
v___y_1165_ = v___y_1066_;
v___y_1166_ = v___y_1067_;
goto v___jp_1162_;
}
v___jp_1069_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; size_t v_sz_1083_; size_t v___x_1084_; lean_object* v___x_9134__overap_1085_; lean_object* v___x_1086_; 
v___x_1078_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__1);
v___x_1079_ = lean_mk_array(v___y_1073_, v___x_1078_);
v___x_1080_ = lean_array_get_size(v___y_1071_);
v___x_1081_ = l_Array_toSubarray___redArg(v___y_1071_, v___y_1070_, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1079_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v_sz_1083_ = lean_array_size(v_positions_1047_);
v___x_1084_ = ((size_t)0ULL);
lean_inc_ref(v___x_1048_);
v___x_9134__overap_1085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1048_, v_positions_1047_, v___f_1049_, v_sz_1083_, v___x_1084_, v___x_1082_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1086_ = lean_apply_5(v___x_9134__overap_1085_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v_fst_1088_; size_t v_sz_1089_; lean_object* v___x_9137__overap_1090_; lean_object* v___x_1091_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v_fst_1088_ = lean_ctor_get(v_a_1087_, 0);
lean_inc(v_fst_1088_);
lean_dec(v_a_1087_);
v_sz_1089_ = lean_array_size(v_fst_1088_);
lean_inc_ref(v___x_1048_);
v___x_9137__overap_1090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1048_, v___f_1050_, v_sz_1089_, v___x_1084_, v_fst_1088_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1091_ = lean_apply_5(v___x_9137__overap_1090_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; uint8_t v___x_1093_; lean_object* v___x_9141__overap_1094_; lean_object* v___x_1095_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v___x_1093_ = 0;
v___x_9141__overap_1094_ = l_Lean_Meta_withLocalDeclsD___redArg(v___x_1051_, v___x_1048_, v_a_1092_, v___y_1072_, v___x_1093_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1095_ = lean_apply_5(v___x_9141__overap_1094_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
return v___x_1095_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v___y_1072_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___x_1048_);
v_a_1096_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1091_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1091_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v___y_1072_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___x_1048_);
v_a_1104_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1086_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1086_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
v___jp_1112_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1121_ = l_Array_toSubarray___redArg(v_args_1063_, v_lower_1119_, v_upper_1120_);
v___x_1122_ = l_Subarray_copy___redArg(v___y_1113_);
v___x_1123_ = l_Lean_mkAppN(v_f_1062_, v___x_1122_);
lean_dec_ref(v___x_1122_);
lean_inc_ref(v___x_1123_);
v___x_1124_ = l_Lean_Meta_inferArgumentTypesN(v_numTypeFormers_1052_, v___x_1123_, v___y_1118_, v___y_1114_, v___y_1117_, v___y_1116_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc_n(v_a_1125_, 2);
lean_dec_ref_known(v___x_1124_, 1);
lean_inc_ref(v___f_1059_);
lean_inc_ref(v___x_1058_);
lean_inc_ref(v_toMonadRef_1057_);
lean_inc_ref(v___x_1056_);
lean_inc(v___x_1055_);
lean_inc_ref(v_positions_1047_);
lean_inc_ref(v___x_1048_);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___boxed), 18, 12);
lean_closure_set(v___f_1126_, 0, v___x_1048_);
lean_closure_set(v___f_1126_, 1, v___x_1053_);
lean_closure_set(v___f_1126_, 2, v_positions_1047_);
lean_closure_set(v___f_1126_, 3, v_a_1125_);
lean_closure_set(v___f_1126_, 4, v___x_1123_);
lean_closure_set(v___f_1126_, 5, v___x_1121_);
lean_closure_set(v___f_1126_, 6, v_k_1054_);
lean_closure_set(v___f_1126_, 7, v___x_1055_);
lean_closure_set(v___f_1126_, 8, v___x_1056_);
lean_closure_set(v___f_1126_, 9, v_toMonadRef_1057_);
lean_closure_set(v___f_1126_, 10, v___x_1058_);
lean_closure_set(v___f_1126_, 11, v___f_1059_);
v___x_1127_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_1047_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1118_);
v___x_1128_ = lean_apply_5(v___f_1059_, v___y_1118_, v___y_1114_, v___y_1117_, v___y_1116_, lean_box(0));
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; uint8_t v___x_1130_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc(v_a_1129_);
lean_dec_ref_known(v___x_1128_, 1);
v___x_1130_ = lean_unbox(v_a_1129_);
lean_dec(v_a_1129_);
if (v___x_1130_ == 0)
{
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_toMonadRef_1057_);
lean_dec_ref(v___x_1056_);
lean_dec(v___x_1055_);
v___y_1070_ = v___y_1115_;
v___y_1071_ = v_a_1125_;
v___y_1072_ = v___f_1126_;
v___y_1073_ = v___x_1127_;
v___y_1074_ = v___y_1118_;
v___y_1075_ = v___y_1114_;
v___y_1076_ = v___y_1117_;
v___y_1077_ = v___y_1116_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_9173__overap_1136_; lean_object* v___x_1137_; 
v___x_1131_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___closed__3);
lean_inc(v___x_1127_);
v___x_1132_ = l_Nat_reprFast(v___x_1127_);
v___x_1133_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
v___x_1134_ = l_Lean_MessageData_ofFormat(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1131_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
lean_inc_ref(v___x_1048_);
v___x_9173__overap_1136_ = l_Lean_addTrace___redArg(v___x_1048_, v___x_1056_, v_toMonadRef_1057_, v___x_1058_, v___x_1055_, v___x_1135_);
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1117_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1118_);
v___x_1137_ = lean_apply_5(v___x_9173__overap_1136_, v___y_1118_, v___y_1114_, v___y_1117_, v___y_1116_, lean_box(0));
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_dec_ref_known(v___x_1137_, 1);
v___y_1070_ = v___y_1115_;
v___y_1071_ = v_a_1125_;
v___y_1072_ = v___f_1126_;
v___y_1073_ = v___x_1127_;
v___y_1074_ = v___y_1118_;
v___y_1075_ = v___y_1114_;
v___y_1076_ = v___y_1117_;
v___y_1077_ = v___y_1116_;
goto v___jp_1069_;
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v___x_1127_);
lean_dec_ref(v___f_1126_);
lean_dec(v_a_1125_);
lean_dec(v___y_1115_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_positions_1047_);
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1137_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1137_);
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
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v___x_1127_);
lean_dec_ref(v___f_1126_);
lean_dec(v_a_1125_);
lean_dec(v___y_1115_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_toMonadRef_1057_);
lean_dec_ref(v___x_1056_);
lean_dec(v___x_1055_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_positions_1047_);
v_a_1146_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1128_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1128_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v___x_1123_);
lean_dec_ref(v___x_1121_);
lean_dec(v___y_1115_);
lean_dec_ref(v___f_1059_);
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_toMonadRef_1057_);
lean_dec_ref(v___x_1056_);
lean_dec(v___x_1055_);
lean_dec_ref(v_k_1054_);
lean_dec_ref(v___x_1053_);
lean_dec_ref(v___x_1051_);
lean_dec_ref(v___f_1050_);
lean_dec_ref(v___f_1049_);
lean_dec_ref(v___x_1048_);
lean_dec_ref(v_positions_1047_);
v_a_1154_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1124_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1124_);
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
v___jp_1162_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
lean_inc(v_numIndParams_1060_);
lean_inc_ref(v_args_1063_);
v___x_1168_ = l_Array_toSubarray___redArg(v_args_1063_, v___x_1167_, v_numIndParams_1060_);
v___x_1169_ = lean_nat_add(v_numIndParams_1060_, v_numTypeFormers_1052_);
lean_dec(v_numIndParams_1060_);
v___x_1170_ = lean_array_get_size(v_args_1063_);
v___x_1171_ = lean_nat_dec_le(v___x_1169_, v___x_1167_);
if (v___x_1171_ == 0)
{
v___y_1113_ = v___x_1168_;
v___y_1114_ = v___y_1164_;
v___y_1115_ = v___x_1167_;
v___y_1116_ = v___y_1166_;
v___y_1117_ = v___y_1165_;
v___y_1118_ = v___y_1163_;
v_lower_1119_ = v___x_1169_;
v_upper_1120_ = v___x_1170_;
goto v___jp_1112_;
}
else
{
lean_dec(v___x_1169_);
v___y_1113_ = v___x_1168_;
v___y_1114_ = v___y_1164_;
v___y_1115_ = v___x_1167_;
v___y_1116_ = v___y_1166_;
v___y_1117_ = v___y_1165_;
v___y_1118_ = v___y_1163_;
v_lower_1119_ = v___x_1167_;
v_upper_1120_ = v___x_1170_;
goto v___jp_1112_;
}
}
v___jp_1172_:
{
lean_object* v___x_1177_; lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v___x_1177_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed___redArg(v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1177_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1177_);
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
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_positions_1047_ = stack[0].m_obj;
lean_object* v___x_1048_ = stack[1].m_obj;
lean_object* v___f_1049_ = stack[2].m_obj;
lean_object* v___f_1050_ = stack[3].m_obj;
lean_object* v___x_1051_ = stack[4].m_obj;
lean_object* v_numTypeFormers_1052_ = stack[5].m_obj;
lean_object* v___x_1053_ = stack[6].m_obj;
lean_object* v_k_1054_ = stack[7].m_obj;
lean_object* v___x_1055_ = stack[8].m_obj;
lean_object* v___x_1056_ = stack[9].m_obj;
lean_object* v_toMonadRef_1057_ = stack[10].m_obj;
lean_object* v___x_1058_ = stack[11].m_obj;
lean_object* v___f_1059_ = stack[12].m_obj;
lean_object* v_numIndParams_1060_ = stack[13].m_obj;
lean_object* v_a_1061_ = stack[14].m_obj;
lean_object* v_f_1062_ = stack[15].m_obj;
lean_object* v_args_1063_ = stack[16].m_obj;
lean_object* v___y_1064_ = stack[17].m_obj;
lean_object* v___y_1065_ = stack[18].m_obj;
lean_object* v___y_1066_ = stack[19].m_obj;
lean_object* v___y_1067_ = stack[20].m_obj;
lean_object* v_res_1213_;
v_res_1213_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1047_, v___x_1048_, v___f_1049_, v___f_1050_, v___x_1051_, v_numTypeFormers_1052_, v___x_1053_, v_k_1054_, v___x_1055_, v___x_1056_, v_toMonadRef_1057_, v___x_1058_, v___f_1059_, v_numIndParams_1060_, v_a_1061_, v_f_1062_, v_args_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
stack->m_obj
 = v_res_1213_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed(lean_object** _args){
lean_object* v_positions_1214_ = _args[0];
lean_object* v___x_1215_ = _args[1];
lean_object* v___f_1216_ = _args[2];
lean_object* v___f_1217_ = _args[3];
lean_object* v___x_1218_ = _args[4];
lean_object* v_numTypeFormers_1219_ = _args[5];
lean_object* v___x_1220_ = _args[6];
lean_object* v_k_1221_ = _args[7];
lean_object* v___x_1222_ = _args[8];
lean_object* v___x_1223_ = _args[9];
lean_object* v_toMonadRef_1224_ = _args[10];
lean_object* v___x_1225_ = _args[11];
lean_object* v___f_1226_ = _args[12];
lean_object* v_numIndParams_1227_ = _args[13];
lean_object* v_a_1228_ = _args[14];
lean_object* v_f_1229_ = _args[15];
lean_object* v_args_1230_ = _args[16];
lean_object* v___y_1231_ = _args[17];
lean_object* v___y_1232_ = _args[18];
lean_object* v___y_1233_ = _args[19];
lean_object* v___y_1234_ = _args[20];
lean_object* v___y_1235_ = _args[21];
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6(v_positions_1214_, v___x_1215_, v___f_1216_, v___f_1217_, v___x_1218_, v_numTypeFormers_1219_, v___x_1220_, v_k_1221_, v___x_1222_, v___x_1223_, v_toMonadRef_1224_, v___x_1225_, v___f_1226_, v_numIndParams_1227_, v_a_1228_, v_f_1229_, v_args_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1236_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0(void){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_instMonadEIO___redArg();
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1238_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__0);
v___x_1239_ = l_StateRefT_x27_instMonad___redArg(v___x_1238_);
return v___x_1239_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = l_Lean_Core_instMonadTraceCoreM;
v___x_1247_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1248_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_1247_, v___x_1246_);
return v___x_1248_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__8);
v___f_1250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___x_1251_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_1250_, v___x_1249_);
return v___x_1251_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__7));
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__11));
v___x_1257_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_1256_, v___x_1255_, v___x_1254_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; 
v___x_1258_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__12);
v___f_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__6));
v___f_1260_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__10));
v___x_1261_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_1260_, v___f_1259_, v___x_1258_);
return v___x_1261_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_1267_ = l_Lean_Name_append(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__17));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(lean_object* v_below_1271_, lean_object* v_numIndParams_1272_, lean_object* v_positions_1273_, lean_object* v_k_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; lean_object* v_toApplicative_1281_; lean_object* v_toFunctor_1282_; lean_object* v_toSeq_1283_; lean_object* v_toSeqLeft_1284_; lean_object* v_toSeqRight_1285_; lean_object* v___f_1286_; lean_object* v___f_1287_; lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_toApplicative_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1425_; 
v___x_1280_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_1281_ = lean_ctor_get(v___x_1280_, 0);
v_toFunctor_1282_ = lean_ctor_get(v_toApplicative_1281_, 0);
v_toSeq_1283_ = lean_ctor_get(v_toApplicative_1281_, 2);
v_toSeqLeft_1284_ = lean_ctor_get(v_toApplicative_1281_, 3);
v_toSeqRight_1285_ = lean_ctor_get(v_toApplicative_1281_, 4);
v___f_1286_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_1287_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1282_, 2);
v___f_1288_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1288_, 0, v_toFunctor_1282_);
v___f_1289_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1289_, 0, v_toFunctor_1282_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___f_1288_);
lean_ctor_set(v___x_1290_, 1, v___f_1289_);
lean_inc(v_toSeqRight_1285_);
v___f_1291_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1291_, 0, v_toSeqRight_1285_);
lean_inc(v_toSeqLeft_1284_);
v___f_1292_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1292_, 0, v_toSeqLeft_1284_);
lean_inc(v_toSeq_1283_);
v___f_1293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1293_, 0, v_toSeq_1283_);
v___x_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1290_);
lean_ctor_set(v___x_1294_, 1, v___f_1286_);
lean_ctor_set(v___x_1294_, 2, v___f_1293_);
lean_ctor_set(v___x_1294_, 3, v___f_1292_);
lean_ctor_set(v___x_1294_, 4, v___f_1291_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
lean_ctor_set(v___x_1295_, 1, v___f_1287_);
v___x_1296_ = l_StateRefT_x27_instMonad___redArg(v___x_1295_);
v_toApplicative_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v___x_1296_, 1);
lean_dec(v_unused_1426_);
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1425_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_toApplicative_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1425_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_toFunctor_1301_; lean_object* v_toSeq_1302_; lean_object* v_toSeqLeft_1303_; lean_object* v_toSeqRight_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1423_; 
v_toFunctor_1301_ = lean_ctor_get(v_toApplicative_1297_, 0);
v_toSeq_1302_ = lean_ctor_get(v_toApplicative_1297_, 2);
v_toSeqLeft_1303_ = lean_ctor_get(v_toApplicative_1297_, 3);
v_toSeqRight_1304_ = lean_ctor_get(v_toApplicative_1297_, 4);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_toApplicative_1297_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_toApplicative_1297_, 1);
lean_dec(v_unused_1424_);
v___x_1306_ = v_toApplicative_1297_;
v_isShared_1307_ = v_isSharedCheck_1423_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_toSeqRight_1304_);
lean_inc(v_toSeqLeft_1303_);
lean_inc(v_toSeq_1302_);
lean_inc(v_toFunctor_1301_);
lean_dec(v_toApplicative_1297_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1423_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___f_1308_; lean_object* v___f_1309_; lean_object* v___f_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; lean_object* v___f_1313_; lean_object* v___f_1314_; lean_object* v___f_1315_; lean_object* v___x_1317_; 
v___f_1308_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_1309_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_1301_);
v___f_1310_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1310_, 0, v_toFunctor_1301_);
v___f_1311_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1311_, 0, v_toFunctor_1301_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___f_1310_);
lean_ctor_set(v___x_1312_, 1, v___f_1311_);
v___f_1313_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1313_, 0, v_toSeqRight_1304_);
v___f_1314_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1314_, 0, v_toSeqLeft_1303_);
v___f_1315_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1315_, 0, v_toSeq_1302_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 4, v___f_1313_);
lean_ctor_set(v___x_1306_, 3, v___f_1314_);
lean_ctor_set(v___x_1306_, 2, v___f_1315_);
lean_ctor_set(v___x_1306_, 1, v___f_1308_);
lean_ctor_set(v___x_1306_, 0, v___x_1312_);
v___x_1317_ = v___x_1306_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___f_1308_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v___f_1315_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v___f_1314_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v___f_1313_);
v___x_1317_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1319_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 1, v___f_1309_);
lean_ctor_set(v___x_1299_, 0, v___x_1317_);
v___x_1319_ = v___x_1299_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___f_1309_);
v___x_1319_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v_toApplicative_1321_; lean_object* v_toFunctor_1322_; lean_object* v_toSeq_1323_; lean_object* v_toSeqLeft_1324_; lean_object* v_toSeqRight_1325_; lean_object* v___f_1326_; lean_object* v___f_1327_; lean_object* v___x_1328_; lean_object* v___f_1329_; lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_toMonadRef_1338_; lean_object* v___f_1339_; lean_object* v___f_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v_numTypeFormers_1343_; lean_object* v___x_1344_; 
v___x_1320_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__9);
v_toApplicative_1321_ = lean_ctor_get(v___x_1280_, 0);
v_toFunctor_1322_ = lean_ctor_get(v_toApplicative_1321_, 0);
v_toSeq_1323_ = lean_ctor_get(v_toApplicative_1321_, 2);
v_toSeqLeft_1324_ = lean_ctor_get(v_toApplicative_1321_, 3);
v_toSeqRight_1325_ = lean_ctor_get(v_toApplicative_1321_, 4);
lean_inc_ref_n(v_toFunctor_1322_, 2);
v___f_1326_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1326_, 0, v_toFunctor_1322_);
v___f_1327_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1327_, 0, v_toFunctor_1322_);
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___f_1326_);
lean_ctor_set(v___x_1328_, 1, v___f_1327_);
lean_inc(v_toSeqRight_1325_);
v___f_1329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1329_, 0, v_toSeqRight_1325_);
lean_inc(v_toSeqLeft_1324_);
v___f_1330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1330_, 0, v_toSeqLeft_1324_);
lean_inc(v_toSeq_1323_);
v___f_1331_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1331_, 0, v_toSeq_1323_);
v___x_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1328_);
lean_ctor_set(v___x_1332_, 1, v___f_1286_);
lean_ctor_set(v___x_1332_, 2, v___f_1331_);
lean_ctor_set(v___x_1332_, 3, v___f_1330_);
lean_ctor_set(v___x_1332_, 4, v___f_1329_);
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___f_1287_);
v___x_1334_ = l_StateRefT_x27_instMonad___redArg(v___x_1333_);
v___x_1335_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_1335_, 0, lean_box(0));
lean_closure_set(v___x_1335_, 1, lean_box(0));
lean_closure_set(v___x_1335_, 2, v___x_1334_);
v___x_1336_ = l_instMonadControlTOfPure___redArg(v___x_1335_);
v___x_1337_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__13);
v_toMonadRef_1338_ = lean_ctor_get(v___x_1337_, 0);
v___f_1339_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__14));
lean_inc_ref(v___x_1319_);
v___f_1340_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__3___boxed), 9, 1);
lean_closure_set(v___f_1340_, 0, v___x_1319_);
v___x_1341_ = l_Lean_instInhabitedExpr;
v___x_1342_ = l_Lean_Meta_instAddMessageContextMetaM;
v_numTypeFormers_1343_ = lean_array_get_size(v_positions_1273_);
lean_inc(v_a_1278_);
lean_inc_ref(v_a_1277_);
lean_inc(v_a_1276_);
lean_inc_ref(v_a_1275_);
lean_inc_ref(v_below_1271_);
v___x_1344_ = lean_infer_type(v_below_1271_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___f_1348_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___x_1397_; lean_object* v_a_1398_; uint8_t v___x_1399_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc_n(v_a_1345_, 2);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___f_1347_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__15));
lean_inc_ref(v_toMonadRef_1338_);
lean_inc_ref(v___x_1319_);
v___f_1348_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__6___boxed), 22, 15);
lean_closure_set(v___f_1348_, 0, v_positions_1273_);
lean_closure_set(v___f_1348_, 1, v___x_1319_);
lean_closure_set(v___f_1348_, 2, v___f_1340_);
lean_closure_set(v___f_1348_, 3, v___f_1339_);
lean_closure_set(v___f_1348_, 4, v___x_1336_);
lean_closure_set(v___f_1348_, 5, v_numTypeFormers_1343_);
lean_closure_set(v___f_1348_, 6, v___x_1341_);
lean_closure_set(v___f_1348_, 7, v_k_1274_);
lean_closure_set(v___f_1348_, 8, v___x_1346_);
lean_closure_set(v___f_1348_, 9, v___x_1320_);
lean_closure_set(v___f_1348_, 10, v_toMonadRef_1338_);
lean_closure_set(v___f_1348_, 11, v___x_1342_);
lean_closure_set(v___f_1348_, 12, v___f_1347_);
lean_closure_set(v___f_1348_, 13, v_numIndParams_1272_);
lean_closure_set(v___f_1348_, 14, v_a_1345_);
v___x_1397_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1346_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref(v___x_1397_);
v___x_1399_ = lean_unbox(v_a_1398_);
lean_dec(v_a_1398_);
if (v___x_1399_ == 0)
{
v___y_1362_ = v_a_1275_;
v___y_1363_ = v_a_1276_;
v___y_1364_ = v_a_1277_;
v___y_1365_ = v_a_1278_;
goto v___jp_1361_;
}
else
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_8829__overap_1403_; lean_object* v___x_1404_; 
v___x_1400_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__18);
lean_inc(v_a_1345_);
v___x_1401_ = l_Lean_MessageData_ofExpr(v_a_1345_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
lean_inc_ref(v_toMonadRef_1338_);
lean_inc_ref(v___x_1319_);
v___x_8829__overap_1403_ = l_Lean_addTrace___redArg(v___x_1319_, v___x_1320_, v_toMonadRef_1338_, v___x_1342_, v___x_1346_, v___x_1402_);
lean_inc(v_a_1278_);
lean_inc_ref(v_a_1277_);
lean_inc(v_a_1276_);
lean_inc_ref(v_a_1275_);
v___x_1404_ = lean_apply_5(v___x_8829__overap_1403_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, lean_box(0));
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_dec_ref_known(v___x_1404_, 1);
v___y_1362_ = v_a_1275_;
v___y_1363_ = v_a_1276_;
v___y_1364_ = v_a_1277_;
v___y_1365_ = v_a_1278_;
goto v___jp_1361_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v___f_1348_);
lean_dec(v_a_1345_);
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_below_1271_);
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
v___jp_1349_:
{
lean_object* v_dummy_1354_; lean_object* v_nargs_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_8825__overap_1359_; lean_object* v___x_1360_; 
v_dummy_1354_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_1355_ = l_Lean_Expr_getAppNumArgs(v_a_1345_);
lean_inc(v_nargs_1355_);
v___x_1356_ = lean_mk_array(v_nargs_1355_, v_dummy_1354_);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_sub(v_nargs_1355_, v___x_1357_);
lean_dec(v_nargs_1355_);
v___x_8825__overap_1359_ = l_Lean_Expr_withAppAux___redArg(v___f_1348_, v_a_1345_, v___x_1356_, v___x_1358_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
v___x_1360_ = lean_apply_5(v___x_8825__overap_1359_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, lean_box(0));
return v___x_1360_;
}
v___jp_1361_:
{
lean_object* v_toCold_1366_; lean_object* v_options_1367_; uint8_t v_hasTrace_1368_; 
v_toCold_1366_ = lean_ctor_get(v___y_1364_, 0);
v_options_1367_ = lean_ctor_get(v_toCold_1366_, 2);
v_hasTrace_1368_ = lean_ctor_get_uint8(v_options_1367_, sizeof(void*)*1);
if (v_hasTrace_1368_ == 0)
{
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_below_1271_);
v___y_1350_ = v___y_1362_;
v___y_1351_ = v___y_1363_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v___y_1365_;
goto v___jp_1349_;
}
else
{
lean_object* v_inheritedTraceOptions_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; 
v_inheritedTraceOptions_1369_ = lean_ctor_get(v_toCold_1366_, 11);
v___x_1370_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1371_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1369_, v_options_1367_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_below_1271_);
v___y_1350_ = v___y_1362_;
v___y_1351_ = v___y_1363_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v___y_1365_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Meta_isTypeCorrect(v_below_1271_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; uint8_t v___x_1374_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_a_1373_);
lean_dec_ref_known(v___x_1372_, 1);
v___x_1374_ = lean_unbox(v_a_1373_);
lean_dec(v_a_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v_a_1376_; uint8_t v___x_1377_; 
v___x_1375_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__4(v___x_1346_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref(v___x_1375_);
v___x_1377_ = lean_unbox(v_a_1376_);
lean_dec(v_a_1376_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v___x_1319_);
v___y_1350_ = v___y_1362_;
v___y_1351_ = v___y_1363_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v___y_1365_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1378_; lean_object* v___x_8827__overap_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__2);
lean_inc_ref(v_toMonadRef_1338_);
v___x_8827__overap_1379_ = l_Lean_addTrace___redArg(v___x_1319_, v___x_1320_, v_toMonadRef_1338_, v___x_1342_, v___x_1346_, v___x_1378_);
lean_inc(v___y_1365_);
lean_inc_ref(v___y_1364_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
v___x_1380_ = lean_apply_5(v___x_8827__overap_1379_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, lean_box(0));
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_dec_ref_known(v___x_1380_, 1);
v___y_1350_ = v___y_1362_;
v___y_1351_ = v___y_1363_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v___y_1365_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v___f_1348_);
lean_dec(v_a_1345_);
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
}
else
{
lean_dec_ref(v___x_1319_);
v___y_1350_ = v___y_1362_;
v___y_1351_ = v___y_1363_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v___y_1365_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v___f_1348_);
lean_dec(v_a_1345_);
lean_dec_ref(v___x_1319_);
v_a_1389_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1372_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1372_);
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
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v___f_1340_);
lean_dec_ref(v___x_1336_);
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_k_1274_);
lean_dec_ref(v_positions_1273_);
lean_dec(v_numIndParams_1272_);
lean_dec_ref(v_below_1271_);
v_a_1413_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1344_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1344_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_below_1271_ = stack[0].m_obj;
lean_object* v_numIndParams_1272_ = stack[1].m_obj;
lean_object* v_positions_1273_ = stack[2].m_obj;
lean_object* v_k_1274_ = stack[3].m_obj;
lean_object* v_a_1275_ = stack[4].m_obj;
lean_object* v_a_1276_ = stack[5].m_obj;
lean_object* v_a_1277_ = stack[6].m_obj;
lean_object* v_a_1278_ = stack[7].m_obj;
lean_object* v_res_1427_;
v_res_1427_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1271_, v_numIndParams_1272_, v_positions_1273_, v_k_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
stack->m_obj
 = v_res_1427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___boxed(lean_object* v_below_1428_, lean_object* v_numIndParams_1429_, lean_object* v_positions_1430_, lean_object* v_k_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1428_, v_numIndParams_1429_, v_positions_1430_, v_k_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
return v_res_1437_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_object* v_00_u03b1_1438_, lean_object* v_inst_1439_, lean_object* v_below_1440_, lean_object* v_numIndParams_1441_, lean_object* v_positions_1442_, lean_object* v_k_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1440_, v_numIndParams_1441_, v_positions_1442_, v_k_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1439_ = stack[1].m_obj;
lean_object* v_below_1440_ = stack[2].m_obj;
lean_object* v_numIndParams_1441_ = stack[3].m_obj;
lean_object* v_positions_1442_ = stack[4].m_obj;
lean_object* v_k_1443_ = stack[5].m_obj;
lean_object* v_a_1444_ = stack[6].m_obj;
lean_object* v_a_1445_ = stack[7].m_obj;
lean_object* v_a_1446_ = stack[8].m_obj;
lean_object* v_a_1447_ = stack[9].m_obj;
lean_object* v_res_1450_;
v_res_1450_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(lean_box(0), v_inst_1439_, v_below_1440_, v_numIndParams_1441_, v_positions_1442_, v_k_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
stack->m_obj
 = v_res_1450_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_inst_1452_, lean_object* v_below_1453_, lean_object* v_numIndParams_1454_, lean_object* v_positions_1455_, lean_object* v_k_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict(v_00_u03b1_1451_, v_inst_1452_, v_below_1453_, v_numIndParams_1454_, v_positions_1455_, v_k_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_inst_1452_);
return v_res_1462_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = lean_unsigned_to_nat(32u);
v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = ((size_t)5ULL);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_unsigned_to_nat(32u);
v___x_1469_ = lean_mk_empty_array_with_capacity(v___x_1468_);
v___x_1470_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__0);
v___x_1471_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v___x_1467_);
lean_ctor_set(v___x_1471_, 3, v___x_1467_);
lean_ctor_set_usize(v___x_1471_, 4, v___x_1466_);
return v___x_1471_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v_traceState_1475_; lean_object* v_traces_1476_; lean_object* v___x_1477_; lean_object* v_traceState_1478_; lean_object* v_env_1479_; lean_object* v_nextMacroScope_1480_; lean_object* v_ngen_1481_; lean_object* v_auxDeclNGen_1482_; lean_object* v_cache_1483_; lean_object* v_recordedDeps_1484_; lean_object* v_messages_1485_; lean_object* v_infoState_1486_; lean_object* v_snapshotTasks_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1506_; 
v___x_1474_ = lean_st_ref_get(v___y_1472_);
v_traceState_1475_ = lean_ctor_get(v___x_1474_, 4);
lean_inc_ref(v_traceState_1475_);
lean_dec(v___x_1474_);
v_traces_1476_ = lean_ctor_get(v_traceState_1475_, 0);
lean_inc_ref(v_traces_1476_);
lean_dec_ref(v_traceState_1475_);
v___x_1477_ = lean_st_ref_take(v___y_1472_);
v_traceState_1478_ = lean_ctor_get(v___x_1477_, 4);
v_env_1479_ = lean_ctor_get(v___x_1477_, 0);
v_nextMacroScope_1480_ = lean_ctor_get(v___x_1477_, 1);
v_ngen_1481_ = lean_ctor_get(v___x_1477_, 2);
v_auxDeclNGen_1482_ = lean_ctor_get(v___x_1477_, 3);
v_cache_1483_ = lean_ctor_get(v___x_1477_, 5);
v_recordedDeps_1484_ = lean_ctor_get(v___x_1477_, 6);
v_messages_1485_ = lean_ctor_get(v___x_1477_, 7);
v_infoState_1486_ = lean_ctor_get(v___x_1477_, 8);
v_snapshotTasks_1487_ = lean_ctor_get(v___x_1477_, 9);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1489_ = v___x_1477_;
v_isShared_1490_ = v_isSharedCheck_1506_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_snapshotTasks_1487_);
lean_inc(v_infoState_1486_);
lean_inc(v_messages_1485_);
lean_inc(v_recordedDeps_1484_);
lean_inc(v_cache_1483_);
lean_inc(v_traceState_1478_);
lean_inc(v_auxDeclNGen_1482_);
lean_inc(v_ngen_1481_);
lean_inc(v_nextMacroScope_1480_);
lean_inc(v_env_1479_);
lean_dec(v___x_1477_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1506_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
uint64_t v_tid_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1504_; 
v_tid_1491_ = lean_ctor_get_uint64(v_traceState_1478_, sizeof(void*)*1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v_traceState_1478_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v_traceState_1478_, 0);
lean_dec(v_unused_1505_);
v___x_1493_ = v_traceState_1478_;
v_isShared_1494_ = v_isSharedCheck_1504_;
goto v_resetjp_1492_;
}
else
{
lean_dec(v_traceState_1478_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1504_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___closed__1);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1495_);
lean_ctor_set_uint64(v_reuseFailAlloc_1503_, sizeof(void*)*1, v_tid_1491_);
v___x_1497_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 4, v___x_1497_);
v___x_1499_ = v___x_1489_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_env_1479_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_nextMacroScope_1480_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_ngen_1481_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_auxDeclNGen_1482_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1502_, 5, v_cache_1483_);
lean_ctor_set(v_reuseFailAlloc_1502_, 6, v_recordedDeps_1484_);
lean_ctor_set(v_reuseFailAlloc_1502_, 7, v_messages_1485_);
lean_ctor_set(v_reuseFailAlloc_1502_, 8, v_infoState_1486_);
lean_ctor_set(v_reuseFailAlloc_1502_, 9, v_snapshotTasks_1487_);
v___x_1499_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_st_ref_put(v___y_1472_, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_traces_1476_);
return v___x_1501_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1472_ = stack[0].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1472_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg___boxed(lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1508_);
lean_dec(v___y_1508_);
return v_res_1510_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v___y_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1511_ = stack[0].m_obj;
lean_object* v___y_1512_ = stack[1].m_obj;
lean_object* v___y_1513_ = stack[2].m_obj;
lean_object* v___y_1514_ = stack[3].m_obj;
lean_object* v_res_1517_;
v_res_1517_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
stack->m_obj
 = v_res_1517_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___boxed(lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0(v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(lean_object* v_opts_1524_, lean_object* v_opt_1525_){
_start:
{
lean_object* v_name_1526_; lean_object* v_defValue_1527_; lean_object* v_map_1528_; lean_object* v___x_1529_; 
v_name_1526_ = lean_ctor_get(v_opt_1525_, 0);
v_defValue_1527_ = lean_ctor_get(v_opt_1525_, 1);
v_map_1528_ = lean_ctor_get(v_opts_1524_, 0);
v___x_1529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1528_, v_name_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_unbox(v_defValue_1527_);
return v___x_1530_;
}
else
{
lean_object* v_val_1531_; 
v_val_1531_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v___x_1529_, 1);
if (lean_obj_tag(v_val_1531_) == 1)
{
uint8_t v_v_1532_; 
v_v_1532_ = lean_ctor_get_uint8(v_val_1531_, 0);
lean_dec_ref_known(v_val_1531_, 0);
return v_v_1532_;
}
else
{
uint8_t v___x_1533_; 
lean_dec(v_val_1531_);
v___x_1533_ = lean_unbox(v_defValue_1527_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1524_ = stack[0].m_obj;
lean_object* v_opt_1525_ = stack[1].m_obj;
uint8_t v_res_1534_;
v_res_1534_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1524_, v_opt_1525_);
stack->m_num = v_res_1534_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1___boxed(lean_object* v_opts_1535_, lean_object* v_opt_1536_){
_start:
{
uint8_t v_res_1537_; lean_object* v_r_1538_; 
v_res_1537_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1535_, v_opt_1536_);
lean_dec_ref(v_opt_1536_);
lean_dec_ref(v_opts_1535_);
v_r_1538_ = lean_box(v_res_1537_);
return v_r_1538_;
}
}
lean_object* l_Lean_Elab_Structural_toBelow___lam__0(lean_object* v___x_1539_, lean_object* v_fnIndex_1540_, lean_object* v_recArg_1541_, lean_object* v_below_1542_, lean_object* v_Cs_1543_, lean_object* v_belowDict_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_array_get_borrowed(v___x_1539_, v_Cs_1543_, v_fnIndex_1540_);
lean_inc(v___x_1550_);
v___x_1551_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux(v___x_1550_, v_belowDict_1544_, v_recArg_1541_, v_below_1542_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
return v___x_1551_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_toBelow___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1539_ = stack[0].m_obj;
lean_object* v_fnIndex_1540_ = stack[1].m_obj;
lean_object* v_recArg_1541_ = stack[2].m_obj;
lean_object* v_below_1542_ = stack[3].m_obj;
lean_object* v_Cs_1543_ = stack[4].m_obj;
lean_object* v_belowDict_1544_ = stack[5].m_obj;
lean_object* v___y_1545_ = stack[6].m_obj;
lean_object* v___y_1546_ = stack[7].m_obj;
lean_object* v___y_1547_ = stack[8].m_obj;
lean_object* v___y_1548_ = stack[9].m_obj;
lean_object* v_res_1552_;
v_res_1552_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1539_, v_fnIndex_1540_, v_recArg_1541_, v_below_1542_, v_Cs_1543_, v_belowDict_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
stack->m_obj
 = v_res_1552_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__0___boxed(lean_object* v___x_1553_, lean_object* v_fnIndex_1554_, lean_object* v_recArg_1555_, lean_object* v_below_1556_, lean_object* v_Cs_1557_, lean_object* v_belowDict_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_Elab_Structural_toBelow___lam__0(v___x_1553_, v_fnIndex_1554_, v_recArg_1555_, v_below_1556_, v_Cs_1557_, v_belowDict_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v_Cs_1557_);
lean_dec(v_fnIndex_1554_);
lean_dec_ref(v___x_1553_);
return v_res_1564_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__0));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = ((lean_object*)(l_Lean_Elab_Structural_toBelow___lam__1___closed__2));
v___x_1570_ = l_Lean_stringToMessageData(v___x_1569_);
return v___x_1570_;
}
}
lean_object* l_Lean_Elab_Structural_toBelow___lam__1(lean_object* v_below_1571_, lean_object* v_recArg_1572_, lean_object* v_x_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
v___x_1579_ = lean_infer_type(v_below_1571_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1594_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1594_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1594_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1584_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__1, &l_Lean_Elab_Structural_toBelow___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__1);
v___x_1585_ = l_Lean_MessageData_ofExpr(v_recArg_1572_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_MessageData_ofExpr(v_a_1580_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1590_);
v___x_1592_ = v___x_1582_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec_ref(v_recArg_1572_);
v_a_1595_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1579_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1579_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_toBelow___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_below_1571_ = stack[0].m_obj;
lean_object* v_recArg_1572_ = stack[1].m_obj;
lean_object* v_x_1573_ = stack[2].m_obj;
lean_object* v___y_1574_ = stack[3].m_obj;
lean_object* v___y_1575_ = stack[4].m_obj;
lean_object* v___y_1576_ = stack[5].m_obj;
lean_object* v___y_1577_ = stack[6].m_obj;
lean_object* v_res_1603_;
v_res_1603_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1571_, v_recArg_1572_, v_x_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
stack->m_obj
 = v_res_1603_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___lam__1___boxed(lean_object* v_below_1604_, lean_object* v_recArg_1605_, lean_object* v_x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Elab_Structural_toBelow___lam__1(v_below_1604_, v_recArg_1605_, v_x_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec_ref(v_x_1606_);
return v_res_1612_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(size_t v_sz_1613_, size_t v_i_1614_, lean_object* v_bs_1615_){
_start:
{
uint8_t v___x_1616_; 
v___x_1616_ = lean_usize_dec_lt(v_i_1614_, v_sz_1613_);
if (v___x_1616_ == 0)
{
return v_bs_1615_;
}
else
{
lean_object* v_v_1617_; lean_object* v_msg_1618_; lean_object* v___x_1619_; lean_object* v_bs_x27_1620_; size_t v___x_1621_; size_t v___x_1622_; lean_object* v___x_1623_; 
v_v_1617_ = lean_array_uget_borrowed(v_bs_1615_, v_i_1614_);
v_msg_1618_ = lean_ctor_get(v_v_1617_, 1);
lean_inc_ref(v_msg_1618_);
v___x_1619_ = lean_unsigned_to_nat(0u);
v_bs_x27_1620_ = lean_array_uset(v_bs_1615_, v_i_1614_, v___x_1619_);
v___x_1621_ = ((size_t)1ULL);
v___x_1622_ = lean_usize_add(v_i_1614_, v___x_1621_);
v___x_1623_ = lean_array_uset(v_bs_x27_1620_, v_i_1614_, v_msg_1618_);
v_i_1614_ = v___x_1622_;
v_bs_1615_ = v___x_1623_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1613_ = stack[0].m_num;
size_t v_i_1614_ = stack[1].m_num;
lean_object* v_bs_1615_ = stack[2].m_obj;
lean_object* v_res_1625_;
v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1613_, v_i_1614_, v_bs_1615_);
stack->m_obj
 = v_res_1625_;
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
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(lean_object* v_oldTraces_1632_, lean_object* v_data_1633_, lean_object* v_ref_1634_, lean_object* v_msg_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_toCold_1641_; lean_object* v_currRecDepth_1642_; lean_object* v_ref_1643_; uint16_t v_optionFlags_1644_; uint8_t v_suppressElabErrors_1645_; uint8_t v_isRecordingDeps_1646_; lean_object* v_ref_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_traceState_1650_; lean_object* v_traces_1651_; lean_object* v___x_1652_; size_t v_sz_1653_; size_t v___x_1654_; lean_object* v___x_1655_; lean_object* v_msg_1656_; lean_object* v___x_1657_; lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1696_; 
v_toCold_1641_ = lean_ctor_get(v___y_1638_, 0);
v_currRecDepth_1642_ = lean_ctor_get(v___y_1638_, 1);
v_ref_1643_ = lean_ctor_get(v___y_1638_, 2);
v_optionFlags_1644_ = lean_ctor_get_uint16(v___y_1638_, sizeof(void*)*3);
v_suppressElabErrors_1645_ = lean_ctor_get_uint8(v___y_1638_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1646_ = lean_ctor_get_uint8(v___y_1638_, sizeof(void*)*3 + 3);
v_ref_1647_ = l_Lean_replaceRef(v_ref_1634_, v_ref_1643_);
lean_inc(v_currRecDepth_1642_);
lean_inc_ref(v_toCold_1641_);
v___x_1648_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1648_, 0, v_toCold_1641_);
lean_ctor_set(v___x_1648_, 1, v_currRecDepth_1642_);
lean_ctor_set(v___x_1648_, 2, v_ref_1647_);
lean_ctor_set_uint16(v___x_1648_, sizeof(void*)*3, v_optionFlags_1644_);
lean_ctor_set_uint8(v___x_1648_, sizeof(void*)*3 + 2, v_suppressElabErrors_1645_);
lean_ctor_set_uint8(v___x_1648_, sizeof(void*)*3 + 3, v_isRecordingDeps_1646_);
v___x_1649_ = lean_st_ref_get(v___y_1639_);
v_traceState_1650_ = lean_ctor_get(v___x_1649_, 4);
lean_inc_ref(v_traceState_1650_);
lean_dec(v___x_1649_);
v_traces_1651_ = lean_ctor_get(v_traceState_1650_, 0);
lean_inc_ref(v_traces_1651_);
lean_dec_ref(v_traceState_1650_);
v___x_1652_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1651_);
lean_dec_ref(v_traces_1651_);
v_sz_1653_ = lean_array_size(v___x_1652_);
v___x_1654_ = ((size_t)0ULL);
v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_spec__3(v_sz_1653_, v___x_1654_, v___x_1652_);
v_msg_1656_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1656_, 0, v_data_1633_);
lean_ctor_set(v_msg_1656_, 1, v_msg_1635_);
lean_ctor_set(v_msg_1656_, 2, v___x_1655_);
v___x_1657_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_1656_, v___y_1636_, v___y_1637_, v___x_1648_, v___y_1639_);
lean_dec_ref_known(v___x_1648_, 3);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1696_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1696_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v_traceState_1663_; lean_object* v_env_1664_; lean_object* v_nextMacroScope_1665_; lean_object* v_ngen_1666_; lean_object* v_auxDeclNGen_1667_; lean_object* v_cache_1668_; lean_object* v_recordedDeps_1669_; lean_object* v_messages_1670_; lean_object* v_infoState_1671_; lean_object* v_snapshotTasks_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1695_; 
v___x_1662_ = lean_st_ref_take(v___y_1639_);
v_traceState_1663_ = lean_ctor_get(v___x_1662_, 4);
v_env_1664_ = lean_ctor_get(v___x_1662_, 0);
v_nextMacroScope_1665_ = lean_ctor_get(v___x_1662_, 1);
v_ngen_1666_ = lean_ctor_get(v___x_1662_, 2);
v_auxDeclNGen_1667_ = lean_ctor_get(v___x_1662_, 3);
v_cache_1668_ = lean_ctor_get(v___x_1662_, 5);
v_recordedDeps_1669_ = lean_ctor_get(v___x_1662_, 6);
v_messages_1670_ = lean_ctor_get(v___x_1662_, 7);
v_infoState_1671_ = lean_ctor_get(v___x_1662_, 8);
v_snapshotTasks_1672_ = lean_ctor_get(v___x_1662_, 9);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1674_ = v___x_1662_;
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_snapshotTasks_1672_);
lean_inc(v_infoState_1671_);
lean_inc(v_messages_1670_);
lean_inc(v_recordedDeps_1669_);
lean_inc(v_cache_1668_);
lean_inc(v_traceState_1663_);
lean_inc(v_auxDeclNGen_1667_);
lean_inc(v_ngen_1666_);
lean_inc(v_nextMacroScope_1665_);
lean_inc(v_env_1664_);
lean_dec(v___x_1662_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
uint64_t v_tid_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1693_; 
v_tid_1676_ = lean_ctor_get_uint64(v_traceState_1663_, sizeof(void*)*1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_traceState_1663_);
if (v_isSharedCheck_1693_ == 0)
{
lean_object* v_unused_1694_; 
v_unused_1694_ = lean_ctor_get(v_traceState_1663_, 0);
lean_dec(v_unused_1694_);
v___x_1678_ = v_traceState_1663_;
v_isShared_1679_ = v_isSharedCheck_1693_;
goto v_resetjp_1677_;
}
else
{
lean_dec(v_traceState_1663_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1693_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_ref_1634_);
lean_ctor_set(v___x_1681_, 1, v_a_1658_);
v___x_1682_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1632_, v___x_1681_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1682_);
v___x_1684_ = v___x_1678_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1682_);
lean_ctor_set_uint64(v_reuseFailAlloc_1692_, sizeof(void*)*1, v_tid_1676_);
v___x_1684_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
lean_object* v___x_1686_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 4, v___x_1684_);
v___x_1686_ = v___x_1674_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_env_1664_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_nextMacroScope_1665_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_ngen_1666_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_auxDeclNGen_1667_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1691_, 5, v_cache_1668_);
lean_ctor_set(v_reuseFailAlloc_1691_, 6, v_recordedDeps_1669_);
lean_ctor_set(v_reuseFailAlloc_1691_, 7, v_messages_1670_);
lean_ctor_set(v_reuseFailAlloc_1691_, 8, v_infoState_1671_);
lean_ctor_set(v_reuseFailAlloc_1691_, 9, v_snapshotTasks_1672_);
v___x_1686_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_st_ref_put(v___y_1639_, v___x_1686_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1680_);
v___x_1689_ = v___x_1660_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1680_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1632_ = stack[0].m_obj;
lean_object* v_data_1633_ = stack[1].m_obj;
lean_object* v_ref_1634_ = stack[2].m_obj;
lean_object* v_msg_1635_ = stack[3].m_obj;
lean_object* v___y_1636_ = stack[4].m_obj;
lean_object* v___y_1637_ = stack[5].m_obj;
lean_object* v___y_1638_ = stack[6].m_obj;
lean_object* v___y_1639_ = stack[7].m_obj;
lean_object* v_res_1697_;
v_res_1697_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1632_, v_data_1633_, v_ref_1634_, v_msg_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
stack->m_obj
 = v_res_1697_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1698_, lean_object* v_data_1699_, lean_object* v_ref_1700_, lean_object* v_msg_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1698_, v_data_1699_, v_ref_1700_, v_msg_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(lean_object* v_opts_1708_, lean_object* v_opt_1709_){
_start:
{
lean_object* v_name_1710_; lean_object* v_defValue_1711_; lean_object* v_map_1712_; lean_object* v___x_1713_; 
v_name_1710_ = lean_ctor_get(v_opt_1709_, 0);
v_defValue_1711_ = lean_ctor_get(v_opt_1709_, 1);
v_map_1712_ = lean_ctor_get(v_opts_1708_, 0);
v___x_1713_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1712_, v_name_1710_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_inc(v_defValue_1711_);
return v_defValue_1711_;
}
else
{
lean_object* v_val_1714_; 
v_val_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_val_1714_);
lean_dec_ref_known(v___x_1713_, 1);
if (lean_obj_tag(v_val_1714_) == 3)
{
lean_object* v_v_1715_; 
v_v_1715_ = lean_ctor_get(v_val_1714_, 0);
lean_inc(v_v_1715_);
lean_dec_ref_known(v_val_1714_, 1);
return v_v_1715_;
}
else
{
lean_dec(v_val_1714_);
lean_inc(v_defValue_1711_);
return v_defValue_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5___boxed(lean_object* v_opts_1716_, lean_object* v_opt_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1716_, v_opt_1717_);
lean_dec_ref(v_opt_1717_);
lean_dec_ref(v_opts_1716_);
return v_res_1718_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(lean_object* v_e_1719_){
_start:
{
if (lean_obj_tag(v_e_1719_) == 0)
{
uint8_t v___x_1720_; 
v___x_1720_ = 2;
return v___x_1720_;
}
else
{
lean_object* v_a_1721_; uint8_t v___x_1722_; 
v_a_1721_ = lean_ctor_get(v_e_1719_, 0);
v___x_1722_ = l_Lean_Expr_hasSyntheticSorry(v_a_1721_);
if (v___x_1722_ == 0)
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
else
{
uint8_t v___x_1724_; 
v___x_1724_ = 1;
return v___x_1724_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1719_ = stack[0].m_obj;
uint8_t v_res_1725_;
v_res_1725_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1719_);
stack->m_num = v_res_1725_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4___boxed(lean_object* v_e_1726_){
_start:
{
uint8_t v_res_1727_; lean_object* v_r_1728_; 
v_res_1727_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_e_1726_);
lean_dec_ref(v_e_1726_);
v_r_1728_ = lean_box(v_res_1727_);
return v_r_1728_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
v_a_1731_ = lean_ctor_get(v_x_1729_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v_x_1729_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v_x_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 1);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v_x_1729_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1729_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v_x_1729_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v_x_1729_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 0);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1729_ = stack[0].m_obj;
lean_object* v_res_1747_;
v_res_1747_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1729_);
stack->m_obj
 = v_res_1747_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1748_);
return v_res_1750_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__0));
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
return v___x_1753_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1754_; double v___x_1755_; 
v___x_1754_ = lean_unsigned_to_nat(1000u);
v___x_1755_ = lean_float_of_nat(v___x_1754_);
return v___x_1755_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(lean_object* v_cls_1756_, uint8_t v_collapsed_1757_, lean_object* v_tag_1758_, lean_object* v_opts_1759_, uint8_t v_clsEnabled_1760_, lean_object* v_oldTraces_1761_, lean_object* v_msg_1762_, lean_object* v_resStartStop_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_fst_1769_; lean_object* v_snd_1770_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v_data_1774_; lean_object* v_fst_1785_; lean_object* v_snd_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___y_1790_; lean_object* v_a_1791_; uint8_t v___y_1806_; double v___y_1838_; 
v_fst_1769_ = lean_ctor_get(v_resStartStop_1763_, 0);
lean_inc(v_fst_1769_);
v_snd_1770_ = lean_ctor_get(v_resStartStop_1763_, 1);
lean_inc(v_snd_1770_);
lean_dec_ref(v_resStartStop_1763_);
v_fst_1785_ = lean_ctor_get(v_snd_1770_, 0);
lean_inc(v_fst_1785_);
v_snd_1786_ = lean_ctor_get(v_snd_1770_, 1);
lean_inc(v_snd_1786_);
lean_dec(v_snd_1770_);
v___x_1787_ = l_Lean_trace_profiler;
v___x_1788_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1759_, v___x_1787_);
if (v___x_1788_ == 0)
{
v___y_1806_ = v___x_1788_;
goto v___jp_1805_;
}
else
{
lean_object* v___x_1843_; uint8_t v___x_1844_; 
v___x_1843_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1844_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_opts_1759_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; double v___x_1847_; double v___x_1848_; double v___x_1849_; 
v___x_1845_ = l_Lean_trace_profiler_threshold;
v___x_1846_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1759_, v___x_1845_);
v___x_1847_ = lean_float_of_nat(v___x_1846_);
v___x_1848_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__2);
v___x_1849_ = lean_float_div(v___x_1847_, v___x_1848_);
v___y_1838_ = v___x_1849_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1851_; double v___x_1852_; 
v___x_1850_ = l_Lean_trace_profiler_threshold;
v___x_1851_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__5(v_opts_1759_, v___x_1850_);
v___x_1852_ = lean_float_of_nat(v___x_1851_);
v___y_1838_ = v___x_1852_;
goto v___jp_1837_;
}
}
v___jp_1771_:
{
lean_object* v___x_1775_; 
lean_inc(v___y_1772_);
v___x_1775_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__2(v_oldTraces_1761_, v_data_1774_, v___y_1772_, v___y_1773_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v___x_1776_; 
lean_dec_ref_known(v___x_1775_, 1);
v___x_1776_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1769_);
return v___x_1776_;
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_fst_1769_);
v_a_1777_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1775_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1775_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
v___jp_1789_:
{
uint8_t v_result_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; double v___x_1795_; lean_object* v_data_1796_; 
v_result_1792_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__4(v_fst_1769_);
v___x_1793_ = lean_box(v_result_1792_);
v___x_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1794_, 0, v___x_1793_);
v___x_1795_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
lean_inc_ref(v_tag_1758_);
lean_inc_ref(v___x_1794_);
lean_inc(v_cls_1756_);
v_data_1796_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1796_, 0, v_cls_1756_);
lean_ctor_set(v_data_1796_, 1, v___x_1794_);
lean_ctor_set(v_data_1796_, 2, v_tag_1758_);
lean_ctor_set_float(v_data_1796_, sizeof(void*)*3, v___x_1795_);
lean_ctor_set_float(v_data_1796_, sizeof(void*)*3 + 8, v___x_1795_);
lean_ctor_set_uint8(v_data_1796_, sizeof(void*)*3 + 16, v_collapsed_1757_);
if (v___x_1788_ == 0)
{
lean_dec_ref_known(v___x_1794_, 1);
lean_dec(v_snd_1786_);
lean_dec(v_fst_1785_);
lean_dec_ref(v_tag_1758_);
lean_dec(v_cls_1756_);
v___y_1772_ = v___y_1790_;
v___y_1773_ = v_a_1791_;
v_data_1774_ = v_data_1796_;
goto v___jp_1771_;
}
else
{
lean_object* v_data_1797_; double v___x_1798_; double v___x_1799_; 
lean_dec_ref_known(v_data_1796_, 3);
v_data_1797_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1797_, 0, v_cls_1756_);
lean_ctor_set(v_data_1797_, 1, v___x_1794_);
lean_ctor_set(v_data_1797_, 2, v_tag_1758_);
v___x_1798_ = lean_unbox_float(v_fst_1785_);
lean_dec(v_fst_1785_);
lean_ctor_set_float(v_data_1797_, sizeof(void*)*3, v___x_1798_);
v___x_1799_ = lean_unbox_float(v_snd_1786_);
lean_dec(v_snd_1786_);
lean_ctor_set_float(v_data_1797_, sizeof(void*)*3 + 8, v___x_1799_);
lean_ctor_set_uint8(v_data_1797_, sizeof(void*)*3 + 16, v_collapsed_1757_);
v___y_1772_ = v___y_1790_;
v___y_1773_ = v_a_1791_;
v_data_1774_ = v_data_1797_;
goto v___jp_1771_;
}
}
v___jp_1800_:
{
lean_object* v_ref_1801_; lean_object* v___x_1802_; 
v_ref_1801_ = lean_ctor_get(v___y_1766_, 2);
lean_inc(v___y_1767_);
lean_inc_ref(v___y_1766_);
lean_inc(v___y_1765_);
lean_inc_ref(v___y_1764_);
lean_inc(v_fst_1769_);
v___x_1802_ = lean_apply_6(v_msg_1762_, v_fst_1769_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, lean_box(0));
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1802_, 1);
v___y_1790_ = v_ref_1801_;
v_a_1791_ = v_a_1803_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v___x_1802_, 1);
v___x_1804_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___closed__1);
v___y_1790_ = v_ref_1801_;
v_a_1791_ = v___x_1804_;
goto v___jp_1789_;
}
}
v___jp_1805_:
{
if (v_clsEnabled_1760_ == 0)
{
if (v___y_1806_ == 0)
{
lean_object* v___x_1807_; lean_object* v_traceState_1808_; lean_object* v_env_1809_; lean_object* v_nextMacroScope_1810_; lean_object* v_ngen_1811_; lean_object* v_auxDeclNGen_1812_; lean_object* v_cache_1813_; lean_object* v_recordedDeps_1814_; lean_object* v_messages_1815_; lean_object* v_infoState_1816_; lean_object* v_snapshotTasks_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1836_; 
lean_dec(v_snd_1786_);
lean_dec(v_fst_1785_);
lean_dec_ref(v_msg_1762_);
lean_dec_ref(v_tag_1758_);
lean_dec(v_cls_1756_);
v___x_1807_ = lean_st_ref_take(v___y_1767_);
v_traceState_1808_ = lean_ctor_get(v___x_1807_, 4);
v_env_1809_ = lean_ctor_get(v___x_1807_, 0);
v_nextMacroScope_1810_ = lean_ctor_get(v___x_1807_, 1);
v_ngen_1811_ = lean_ctor_get(v___x_1807_, 2);
v_auxDeclNGen_1812_ = lean_ctor_get(v___x_1807_, 3);
v_cache_1813_ = lean_ctor_get(v___x_1807_, 5);
v_recordedDeps_1814_ = lean_ctor_get(v___x_1807_, 6);
v_messages_1815_ = lean_ctor_get(v___x_1807_, 7);
v_infoState_1816_ = lean_ctor_get(v___x_1807_, 8);
v_snapshotTasks_1817_ = lean_ctor_get(v___x_1807_, 9);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1819_ = v___x_1807_;
v_isShared_1820_ = v_isSharedCheck_1836_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snapshotTasks_1817_);
lean_inc(v_infoState_1816_);
lean_inc(v_messages_1815_);
lean_inc(v_recordedDeps_1814_);
lean_inc(v_cache_1813_);
lean_inc(v_traceState_1808_);
lean_inc(v_auxDeclNGen_1812_);
lean_inc(v_ngen_1811_);
lean_inc(v_nextMacroScope_1810_);
lean_inc(v_env_1809_);
lean_dec(v___x_1807_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1836_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
uint64_t v_tid_1821_; lean_object* v_traces_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1835_; 
v_tid_1821_ = lean_ctor_get_uint64(v_traceState_1808_, sizeof(void*)*1);
v_traces_1822_ = lean_ctor_get(v_traceState_1808_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_traceState_1808_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1824_ = v_traceState_1808_;
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_traces_1822_);
lean_dec(v_traceState_1808_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1761_, v_traces_1822_);
lean_dec_ref(v_traces_1822_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1826_);
v___x_1828_ = v___x_1824_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1826_);
lean_ctor_set_uint64(v_reuseFailAlloc_1834_, sizeof(void*)*1, v_tid_1821_);
v___x_1828_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1830_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 4, v___x_1828_);
v___x_1830_ = v___x_1819_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_env_1809_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_nextMacroScope_1810_);
lean_ctor_set(v_reuseFailAlloc_1833_, 2, v_ngen_1811_);
lean_ctor_set(v_reuseFailAlloc_1833_, 3, v_auxDeclNGen_1812_);
lean_ctor_set(v_reuseFailAlloc_1833_, 4, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1833_, 5, v_cache_1813_);
lean_ctor_set(v_reuseFailAlloc_1833_, 6, v_recordedDeps_1814_);
lean_ctor_set(v_reuseFailAlloc_1833_, 7, v_messages_1815_);
lean_ctor_set(v_reuseFailAlloc_1833_, 8, v_infoState_1816_);
lean_ctor_set(v_reuseFailAlloc_1833_, 9, v_snapshotTasks_1817_);
v___x_1830_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = lean_st_ref_put(v___y_1767_, v___x_1830_);
v___x_1832_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_fst_1769_);
return v___x_1832_;
}
}
}
}
}
else
{
goto v___jp_1800_;
}
}
else
{
goto v___jp_1800_;
}
}
v___jp_1837_:
{
double v___x_1839_; double v___x_1840_; double v___x_1841_; uint8_t v___x_1842_; 
v___x_1839_ = lean_unbox_float(v_snd_1786_);
v___x_1840_ = lean_unbox_float(v_fst_1785_);
v___x_1841_ = lean_float_sub(v___x_1839_, v___x_1840_);
v___x_1842_ = lean_float_decLt(v___y_1838_, v___x_1841_);
v___y_1806_ = v___x_1842_;
goto v___jp_1805_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1756_ = stack[0].m_obj;
uint8_t v_collapsed_1757_ = stack[1].m_num;
lean_object* v_tag_1758_ = stack[2].m_obj;
lean_object* v_opts_1759_ = stack[3].m_obj;
uint8_t v_clsEnabled_1760_ = stack[4].m_num;
lean_object* v_oldTraces_1761_ = stack[5].m_obj;
lean_object* v_msg_1762_ = stack[6].m_obj;
lean_object* v_resStartStop_1763_ = stack[7].m_obj;
lean_object* v___y_1764_ = stack[8].m_obj;
lean_object* v___y_1765_ = stack[9].m_obj;
lean_object* v___y_1766_ = stack[10].m_obj;
lean_object* v___y_1767_ = stack[11].m_obj;
lean_object* v_res_1853_;
v_res_1853_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1756_, v_collapsed_1757_, v_tag_1758_, v_opts_1759_, v_clsEnabled_1760_, v_oldTraces_1761_, v_msg_1762_, v_resStartStop_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
stack->m_obj
 = v_res_1853_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2___boxed(lean_object* v_cls_1854_, lean_object* v_collapsed_1855_, lean_object* v_tag_1856_, lean_object* v_opts_1857_, lean_object* v_clsEnabled_1858_, lean_object* v_oldTraces_1859_, lean_object* v_msg_1860_, lean_object* v_resStartStop_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
uint8_t v_collapsed_boxed_1867_; uint8_t v_clsEnabled_boxed_1868_; lean_object* v_res_1869_; 
v_collapsed_boxed_1867_ = lean_unbox(v_collapsed_1855_);
v_clsEnabled_boxed_1868_ = lean_unbox(v_clsEnabled_1858_);
v_res_1869_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v_cls_1854_, v_collapsed_boxed_1867_, v_tag_1856_, v_opts_1857_, v_clsEnabled_boxed_1868_, v_oldTraces_1859_, v_msg_1860_, v_resStartStop_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v_opts_1857_);
return v_res_1869_;
}
}
static double _init_l_Lean_Elab_Structural_toBelow___closed__0(void){
_start:
{
lean_object* v___x_1870_; double v___x_1871_; 
v___x_1870_ = lean_unsigned_to_nat(1000000000u);
v___x_1871_ = lean_float_of_nat(v___x_1870_);
return v___x_1871_;
}
}
lean_object* l_Lean_Elab_Structural_toBelow(lean_object* v_below_1872_, lean_object* v_numIndParams_1873_, lean_object* v_positions_1874_, lean_object* v_fnIndex_1875_, lean_object* v_recArg_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_toCold_1882_; lean_object* v_options_1883_; lean_object* v_inheritedTraceOptions_1884_; uint8_t v_hasTrace_1885_; lean_object* v___x_1886_; lean_object* v___f_1887_; 
v_toCold_1882_ = lean_ctor_get(v_a_1879_, 0);
v_options_1883_ = lean_ctor_get(v_toCold_1882_, 2);
v_inheritedTraceOptions_1884_ = lean_ctor_get(v_toCold_1882_, 11);
v_hasTrace_1885_ = lean_ctor_get_uint8(v_options_1883_, sizeof(void*)*1);
v___x_1886_ = l_Lean_instInhabitedExpr;
lean_inc_ref(v_below_1872_);
lean_inc_ref(v_recArg_1876_);
v___f_1887_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1887_, 0, v___x_1886_);
lean_closure_set(v___f_1887_, 1, v_fnIndex_1875_);
lean_closure_set(v___f_1887_, 2, v_recArg_1876_);
lean_closure_set(v___f_1887_, 3, v_below_1872_);
if (v_hasTrace_1885_ == 0)
{
lean_object* v___x_1888_; 
lean_dec_ref(v_recArg_1876_);
v___x_1888_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1872_, v_numIndParams_1873_, v_positions_1874_, v___f_1887_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1888_;
}
else
{
lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v_a_1897_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v_a_1912_; 
lean_inc_ref(v_below_1872_);
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_toBelow___lam__1___boxed), 8, 2);
lean_closure_set(v___f_1889_, 0, v_below_1872_);
lean_closure_set(v___f_1889_, 1, v_recArg_1876_);
v___x_1890_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_1891_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_1892_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__16);
v___x_1893_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1884_, v_options_1883_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = l_Lean_trace_profiler;
v___x_1963_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1883_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v___f_1889_);
v___x_1964_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1872_, v_numIndParams_1873_, v_positions_1874_, v___f_1887_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1964_;
}
else
{
goto v___jp_1921_;
}
}
else
{
goto v___jp_1921_;
}
v___jp_1894_:
{
lean_object* v___x_1898_; double v___x_1899_; double v___x_1900_; double v___x_1901_; double v___x_1902_; double v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1898_ = lean_io_mono_nanos_now();
v___x_1899_ = lean_float_of_nat(v___y_1896_);
v___x_1900_ = lean_float_once(&l_Lean_Elab_Structural_toBelow___closed__0, &l_Lean_Elab_Structural_toBelow___closed__0_once, _init_l_Lean_Elab_Structural_toBelow___closed__0);
v___x_1901_ = lean_float_div(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_float_of_nat(v___x_1898_);
v___x_1903_ = lean_float_div(v___x_1902_, v___x_1900_);
v___x_1904_ = lean_box_float(v___x_1901_);
v___x_1905_ = lean_box_float(v___x_1903_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_a_1897_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1890_, v_hasTrace_1885_, v___x_1891_, v_options_1883_, v___x_1893_, v___y_1895_, v___f_1889_, v___x_1907_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1908_;
}
v___jp_1909_:
{
lean_object* v___x_1913_; double v___x_1914_; double v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1913_ = lean_io_get_num_heartbeats();
v___x_1914_ = lean_float_of_nat(v___y_1911_);
v___x_1915_ = lean_float_of_nat(v___x_1913_);
v___x_1916_ = lean_box_float(v___x_1914_);
v___x_1917_ = lean_box_float(v___x_1915_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1912_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2(v___x_1890_, v_hasTrace_1885_, v___x_1891_, v_options_1883_, v___x_1893_, v___y_1910_, v___f_1889_, v___x_1919_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1920_;
}
v___jp_1921_:
{
lean_object* v___x_1922_; lean_object* v_a_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v___x_1922_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Structural_toBelow_spec__0___redArg(v_a_1880_);
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref(v___x_1922_);
v___x_1924_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1925_ = l_Lean_Option_get___at___00Lean_Elab_Structural_toBelow_spec__1(v_options_1883_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1926_ = lean_io_mono_nanos_now();
v___x_1927_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1872_, v_numIndParams_1873_, v_positions_1874_, v___f_1887_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set_tag(v___x_1930_, 1);
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
v___y_1895_ = v_a_1923_;
v___y_1896_ = v___x_1926_;
v_a_1897_ = v___x_1933_;
goto v___jp_1894_;
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_a_1936_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1927_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1927_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 0);
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
v___y_1895_ = v_a_1923_;
v___y_1896_ = v___x_1926_;
v_a_1897_ = v___x_1941_;
goto v___jp_1894_;
}
}
}
}
else
{
lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1944_ = lean_io_get_num_heartbeats();
v___x_1945_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg(v_below_1872_, v_numIndParams_1873_, v_positions_1874_, v___f_1887_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 1);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v___y_1910_ = v_a_1923_;
v___y_1911_ = v___x_1944_;
v_a_1912_ = v___x_1951_;
goto v___jp_1909_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
v_a_1954_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1945_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1945_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 0);
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
v___y_1910_ = v_a_1923_;
v___y_1911_ = v___x_1944_;
v_a_1912_ = v___x_1959_;
goto v___jp_1909_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_toBelow_0interp(lean_interpreter_value* stack)
{
lean_object* v_below_1872_ = stack[0].m_obj;
lean_object* v_numIndParams_1873_ = stack[1].m_obj;
lean_object* v_positions_1874_ = stack[2].m_obj;
lean_object* v_fnIndex_1875_ = stack[3].m_obj;
lean_object* v_recArg_1876_ = stack[4].m_obj;
lean_object* v_a_1877_ = stack[5].m_obj;
lean_object* v_a_1878_ = stack[6].m_obj;
lean_object* v_a_1879_ = stack[7].m_obj;
lean_object* v_a_1880_ = stack[8].m_obj;
lean_object* v_res_1965_;
v_res_1965_ = l_Lean_Elab_Structural_toBelow(v_below_1872_, v_numIndParams_1873_, v_positions_1874_, v_fnIndex_1875_, v_recArg_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
stack->m_obj
 = v_res_1965_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_toBelow___boxed(lean_object* v_below_1966_, lean_object* v_numIndParams_1967_, lean_object* v_positions_1968_, lean_object* v_fnIndex_1969_, lean_object* v_recArg_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Elab_Structural_toBelow(v_below_1966_, v_numIndParams_1967_, v_positions_1968_, v_fnIndex_1969_, v_recArg_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1976_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_object* v_00_u03b1_1977_, lean_object* v_x_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___redArg(v_x_1978_);
return v___x_1984_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1978_ = stack[1].m_obj;
lean_object* v___y_1979_ = stack[2].m_obj;
lean_object* v___y_1980_ = stack[3].m_obj;
lean_object* v___y_1981_ = stack[4].m_obj;
lean_object* v___y_1982_ = stack[5].m_obj;
lean_object* v_res_1985_;
v_res_1985_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(lean_box(0), v_x_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
stack->m_obj
 = v_res_1985_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1986_, lean_object* v_x_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Structural_toBelow_spec__2_spec__3(v_00_u03b1_1986_, v_x_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_1993_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(lean_object* v_k_1994_, lean_object* v___y_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v___x_2002_; 
lean_inc(v___y_2000_);
lean_inc_ref(v___y_1999_);
lean_inc(v___y_1998_);
lean_inc_ref(v___y_1997_);
lean_inc(v___y_1995_);
v___x_2002_ = lean_apply_7(v_k_1994_, v_b_1996_, v___y_1995_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_, lean_box(0));
return v___x_2002_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1994_ = stack[0].m_obj;
lean_object* v___y_1995_ = stack[1].m_obj;
lean_object* v_b_1996_ = stack[2].m_obj;
lean_object* v___y_1997_ = stack[3].m_obj;
lean_object* v___y_1998_ = stack[4].m_obj;
lean_object* v___y_1999_ = stack[5].m_obj;
lean_object* v___y_2000_ = stack[6].m_obj;
lean_object* v_res_2003_;
v_res_2003_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_1994_, v___y_1995_, v_b_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
stack->m_obj
 = v_res_2003_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed(lean_object* v_k_2004_, lean_object* v___y_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0(v_k_2004_, v___y_2005_, v_b_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2005_);
return v_res_2012_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(lean_object* v_name_2013_, uint8_t v_bi_2014_, lean_object* v_type_2015_, lean_object* v_k_2016_, uint8_t v_kind_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___f_2024_; lean_object* v___x_2025_; 
lean_inc(v___y_2018_);
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2024_, 0, v_k_2016_);
lean_closure_set(v___f_2024_, 1, v___y_2018_);
v___x_2025_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2013_, v_bi_2014_, v_type_2015_, v___f_2024_, v_kind_2017_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
if (lean_obj_tag(v___x_2025_) == 0)
{
return v___x_2025_;
}
else
{
lean_object* v_a_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2025_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_a_2026_);
lean_dec(v___x_2025_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2013_ = stack[0].m_obj;
uint8_t v_bi_2014_ = stack[1].m_num;
lean_object* v_type_2015_ = stack[2].m_obj;
lean_object* v_k_2016_ = stack[3].m_obj;
uint8_t v_kind_2017_ = stack[4].m_num;
lean_object* v___y_2018_ = stack[5].m_obj;
lean_object* v___y_2019_ = stack[6].m_obj;
lean_object* v___y_2020_ = stack[7].m_obj;
lean_object* v___y_2021_ = stack[8].m_obj;
lean_object* v___y_2022_ = stack[9].m_obj;
lean_object* v_res_2034_;
v_res_2034_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2013_, v_bi_2014_, v_type_2015_, v_k_2016_, v_kind_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
stack->m_obj
 = v_res_2034_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___boxed(lean_object* v_name_2035_, lean_object* v_bi_2036_, lean_object* v_type_2037_, lean_object* v_k_2038_, lean_object* v_kind_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
uint8_t v_bi_boxed_2046_; uint8_t v_kind_boxed_2047_; lean_object* v_res_2048_; 
v_bi_boxed_2046_ = lean_unbox(v_bi_2036_);
v_kind_boxed_2047_ = lean_unbox(v_kind_2039_);
v_res_2048_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2035_, v_bi_boxed_2046_, v_type_2037_, v_k_2038_, v_kind_boxed_2047_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
return v_res_2048_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_object* v_00_u03b1_2049_, lean_object* v_name_2050_, uint8_t v_bi_2051_, lean_object* v_type_2052_, lean_object* v_k_2053_, uint8_t v_kind_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_name_2050_, v_bi_2051_, v_type_2052_, v_k_2053_, v_kind_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2050_ = stack[1].m_obj;
uint8_t v_bi_2051_ = stack[2].m_num;
lean_object* v_type_2052_ = stack[3].m_obj;
lean_object* v_k_2053_ = stack[4].m_obj;
uint8_t v_kind_2054_ = stack[5].m_num;
lean_object* v___y_2055_ = stack[6].m_obj;
lean_object* v___y_2056_ = stack[7].m_obj;
lean_object* v___y_2057_ = stack[8].m_obj;
lean_object* v___y_2058_ = stack[9].m_obj;
lean_object* v___y_2059_ = stack[10].m_obj;
lean_object* v_res_2062_;
v_res_2062_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(lean_box(0), v_name_2050_, v_bi_2051_, v_type_2052_, v_k_2053_, v_kind_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
stack->m_obj
 = v_res_2062_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___boxed(lean_object* v_00_u03b1_2063_, lean_object* v_name_2064_, lean_object* v_bi_2065_, lean_object* v_type_2066_, lean_object* v_k_2067_, lean_object* v_kind_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
uint8_t v_bi_boxed_2075_; uint8_t v_kind_boxed_2076_; lean_object* v_res_2077_; 
v_bi_boxed_2075_ = lean_unbox(v_bi_2065_);
v_kind_boxed_2076_ = lean_unbox(v_kind_2068_);
v_res_2077_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3(v_00_u03b1_2063_, v_name_2064_, v_bi_boxed_2075_, v_type_2066_, v_k_2067_, v_kind_boxed_2076_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
return v_res_2077_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(lean_object* v_k_2078_, lean_object* v___y_2079_, lean_object* v_b_2080_, lean_object* v_c_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
lean_inc(v___y_2085_);
lean_inc_ref(v___y_2084_);
lean_inc(v___y_2083_);
lean_inc_ref(v___y_2082_);
lean_inc(v___y_2079_);
v___x_2087_ = lean_apply_8(v_k_2078_, v_b_2080_, v_c_2081_, v___y_2079_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, lean_box(0));
return v___x_2087_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2078_ = stack[0].m_obj;
lean_object* v___y_2079_ = stack[1].m_obj;
lean_object* v_b_2080_ = stack[2].m_obj;
lean_object* v_c_2081_ = stack[3].m_obj;
lean_object* v___y_2082_ = stack[4].m_obj;
lean_object* v___y_2083_ = stack[5].m_obj;
lean_object* v___y_2084_ = stack[6].m_obj;
lean_object* v___y_2085_ = stack[7].m_obj;
lean_object* v_res_2088_;
v_res_2088_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___lam__0(v_k_2078_, v___y_2079_, v_b_2080_, v_c_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_);
stack->m_obj
 = v_res_2088_;
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
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(lean_object* v_e_2099_, lean_object* v_maxFVars_2100_, lean_object* v_k_2101_, uint8_t v_cleanupAnnotations_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
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
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2099_ = stack[0].m_obj;
lean_object* v_maxFVars_2100_ = stack[1].m_obj;
lean_object* v_k_2101_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2102_ = stack[3].m_num;
lean_object* v___y_2103_ = stack[4].m_obj;
lean_object* v___y_2104_ = stack[5].m_obj;
lean_object* v___y_2105_ = stack[6].m_obj;
lean_object* v___y_2106_ = stack[7].m_obj;
lean_object* v___y_2107_ = stack[8].m_obj;
lean_object* v_res_2122_;
v_res_2122_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2099_, v_maxFVars_2100_, v_k_2101_, v_cleanupAnnotations_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
stack->m_obj
 = v_res_2122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg___boxed(lean_object* v_e_2123_, lean_object* v_maxFVars_2124_, lean_object* v_k_2125_, lean_object* v_cleanupAnnotations_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2133_; lean_object* v_res_2134_; 
v_cleanupAnnotations_boxed_2133_ = lean_unbox(v_cleanupAnnotations_2126_);
v_res_2134_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2123_, v_maxFVars_2124_, v_k_2125_, v_cleanupAnnotations_boxed_2133_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
return v_res_2134_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_object* v_00_u03b1_2135_, lean_object* v_e_2136_, lean_object* v_maxFVars_2137_, lean_object* v_k_2138_, uint8_t v_cleanupAnnotations_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_e_2136_, v_maxFVars_2137_, v_k_2138_, v_cleanupAnnotations_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2136_ = stack[1].m_obj;
lean_object* v_maxFVars_2137_ = stack[2].m_obj;
lean_object* v_k_2138_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_2139_ = stack[4].m_num;
lean_object* v___y_2140_ = stack[5].m_obj;
lean_object* v___y_2141_ = stack[6].m_obj;
lean_object* v___y_2142_ = stack[7].m_obj;
lean_object* v___y_2143_ = stack[8].m_obj;
lean_object* v___y_2144_ = stack[9].m_obj;
lean_object* v_res_2147_;
v_res_2147_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(lean_box(0), v_e_2136_, v_maxFVars_2137_, v_k_2138_, v_cleanupAnnotations_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
stack->m_obj
 = v_res_2147_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_e_2149_, lean_object* v_maxFVars_2150_, lean_object* v_k_2151_, lean_object* v_cleanupAnnotations_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2159_; lean_object* v_res_2160_; 
v_cleanupAnnotations_boxed_2159_ = lean_unbox(v_cleanupAnnotations_2152_);
v_res_2160_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9(v_00_u03b1_2148_, v_e_2149_, v_maxFVars_2150_, v_k_2151_, v_cleanupAnnotations_boxed_2159_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
return v_res_2160_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(lean_object* v_cls_2161_, lean_object* v_msg_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_ref_2168_; lean_object* v___x_2169_; lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2215_; 
v_ref_2168_ = lean_ctor_get(v___y_2165_, 2);
v___x_2169_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2215_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2215_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v_traceState_2175_; lean_object* v_env_2176_; lean_object* v_nextMacroScope_2177_; lean_object* v_ngen_2178_; lean_object* v_auxDeclNGen_2179_; lean_object* v_cache_2180_; lean_object* v_recordedDeps_2181_; lean_object* v_messages_2182_; lean_object* v_infoState_2183_; lean_object* v_snapshotTasks_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2214_; 
v___x_2174_ = lean_st_ref_take(v___y_2166_);
v_traceState_2175_ = lean_ctor_get(v___x_2174_, 4);
v_env_2176_ = lean_ctor_get(v___x_2174_, 0);
v_nextMacroScope_2177_ = lean_ctor_get(v___x_2174_, 1);
v_ngen_2178_ = lean_ctor_get(v___x_2174_, 2);
v_auxDeclNGen_2179_ = lean_ctor_get(v___x_2174_, 3);
v_cache_2180_ = lean_ctor_get(v___x_2174_, 5);
v_recordedDeps_2181_ = lean_ctor_get(v___x_2174_, 6);
v_messages_2182_ = lean_ctor_get(v___x_2174_, 7);
v_infoState_2183_ = lean_ctor_get(v___x_2174_, 8);
v_snapshotTasks_2184_ = lean_ctor_get(v___x_2174_, 9);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2186_ = v___x_2174_;
v_isShared_2187_ = v_isSharedCheck_2214_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snapshotTasks_2184_);
lean_inc(v_infoState_2183_);
lean_inc(v_messages_2182_);
lean_inc(v_recordedDeps_2181_);
lean_inc(v_cache_2180_);
lean_inc(v_traceState_2175_);
lean_inc(v_auxDeclNGen_2179_);
lean_inc(v_ngen_2178_);
lean_inc(v_nextMacroScope_2177_);
lean_inc(v_env_2176_);
lean_dec(v___x_2174_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2214_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
uint64_t v_tid_2188_; lean_object* v_traces_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2213_; 
v_tid_2188_ = lean_ctor_get_uint64(v_traceState_2175_, sizeof(void*)*1);
v_traces_2189_ = lean_ctor_get(v_traceState_2175_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_traceState_2175_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2191_ = v_traceState_2175_;
v_isShared_2192_ = v_isSharedCheck_2213_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_traces_2189_);
lean_dec(v_traceState_2175_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2213_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; double v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_box(0);
v___x_2195_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__0);
v___x_2196_ = 0;
v___x_2197_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__1));
v___x_2198_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2198_, 0, v_cls_2161_);
lean_ctor_set(v___x_2198_, 1, v___x_2194_);
lean_ctor_set(v___x_2198_, 2, v___x_2197_);
lean_ctor_set_float(v___x_2198_, sizeof(void*)*3, v___x_2195_);
lean_ctor_set_float(v___x_2198_, sizeof(void*)*3 + 8, v___x_2195_);
lean_ctor_set_uint8(v___x_2198_, sizeof(void*)*3 + 16, v___x_2196_);
v___x_2199_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__0___closed__2));
v___x_2200_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v_a_2170_);
lean_ctor_set(v___x_2200_, 2, v___x_2199_);
lean_inc(v_ref_2168_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_ref_2168_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_PersistentArray_push___redArg(v_traces_2189_, v___x_2201_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2202_);
v___x_2204_ = v___x_2191_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2202_);
lean_ctor_set_uint64(v_reuseFailAlloc_2212_, sizeof(void*)*1, v_tid_2188_);
v___x_2204_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v___x_2204_);
v___x_2206_ = v___x_2186_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_env_2176_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_nextMacroScope_2177_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_ngen_2178_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_auxDeclNGen_2179_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2211_, 5, v_cache_2180_);
lean_ctor_set(v_reuseFailAlloc_2211_, 6, v_recordedDeps_2181_);
lean_ctor_set(v_reuseFailAlloc_2211_, 7, v_messages_2182_);
lean_ctor_set(v_reuseFailAlloc_2211_, 8, v_infoState_2183_);
lean_ctor_set(v_reuseFailAlloc_2211_, 9, v_snapshotTasks_2184_);
v___x_2206_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2207_ = lean_st_ref_put(v___y_2166_, v___x_2206_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 0, v___x_2193_);
v___x_2209_ = v___x_2172_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2193_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2161_ = stack[0].m_obj;
lean_object* v_msg_2162_ = stack[1].m_obj;
lean_object* v___y_2163_ = stack[2].m_obj;
lean_object* v___y_2164_ = stack[3].m_obj;
lean_object* v___y_2165_ = stack[4].m_obj;
lean_object* v___y_2166_ = stack[5].m_obj;
lean_object* v_res_2216_;
v_res_2216_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2161_, v_msg_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
stack->m_obj
 = v_res_2216_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg___boxed(lean_object* v_cls_2217_, lean_object* v_msg_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_2217_, v_msg_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2224_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(lean_object* v_e_2225_, lean_object* v_as_2226_, size_t v_i_2227_, size_t v_stop_2228_){
_start:
{
uint8_t v___x_2233_; 
v___x_2233_ = lean_usize_dec_eq(v_i_2227_, v_stop_2228_);
if (v___x_2233_ == 0)
{
lean_object* v___x_2234_; lean_object* v_fnName_2235_; lean_object* v_recArgPos_2236_; uint8_t v___x_2237_; 
v___x_2234_ = lean_array_uget_borrowed(v_as_2226_, v_i_2227_);
v_fnName_2235_ = lean_ctor_get(v___x_2234_, 0);
v_recArgPos_2236_ = lean_ctor_get(v___x_2234_, 2);
lean_inc(v_recArgPos_2236_);
lean_inc(v_fnName_2235_);
v___x_2237_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(v_fnName_2235_, v_recArgPos_2236_, v_e_2225_);
if (v___x_2237_ == 0)
{
goto v___jp_2229_;
}
else
{
if (v___x_2237_ == 0)
{
goto v___jp_2229_;
}
else
{
return v___x_2237_;
}
}
}
else
{
uint8_t v___x_2238_; 
v___x_2238_ = 0;
return v___x_2238_;
}
v___jp_2229_:
{
size_t v___x_2230_; size_t v___x_2231_; 
v___x_2230_ = ((size_t)1ULL);
v___x_2231_ = lean_usize_add(v_i_2227_, v___x_2230_);
v_i_2227_ = v___x_2231_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2225_ = stack[0].m_obj;
lean_object* v_as_2226_ = stack[1].m_obj;
size_t v_i_2227_ = stack[2].m_num;
size_t v_stop_2228_ = stack[3].m_num;
uint8_t v_res_2239_;
v_res_2239_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2225_, v_as_2226_, v_i_2227_, v_stop_2228_);
stack->m_num = v_res_2239_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6___boxed(lean_object* v_e_2240_, lean_object* v_as_2241_, lean_object* v_i_2242_, lean_object* v_stop_2243_){
_start:
{
size_t v_i_boxed_2244_; size_t v_stop_boxed_2245_; uint8_t v_res_2246_; lean_object* v_r_2247_; 
v_i_boxed_2244_ = lean_unbox_usize(v_i_2242_);
lean_dec(v_i_2242_);
v_stop_boxed_2245_ = lean_unbox_usize(v_stop_2243_);
lean_dec(v_stop_2243_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_2240_, v_as_2241_, v_i_boxed_2244_, v_stop_boxed_2245_);
lean_dec_ref(v_as_2241_);
lean_dec_ref(v_e_2240_);
v_r_2247_ = lean_box(v_res_2246_);
return v_r_2247_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(lean_object* v___x_2248_, lean_object* v_____do__lift_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v_toCold_2256_; lean_object* v_options_2257_; uint8_t v_hasTrace_2258_; 
v_toCold_2256_ = lean_ctor_get(v___y_2253_, 0);
v_options_2257_ = lean_ctor_get(v_toCold_2256_, 2);
v_hasTrace_2258_ = lean_ctor_get_uint8(v_options_2257_, sizeof(void*)*1);
if (v_hasTrace_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_dec(v___x_2248_);
v___x_2259_ = lean_box(v_hasTrace_2258_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
v___x_2262_ = l_Lean_Name_append(v___x_2261_, v___x_2248_);
v___x_2263_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_____do__lift_2249_, v_options_2257_, v___x_2262_);
lean_dec(v___x_2262_);
v___x_2264_ = lean_box(v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
return v___x_2265_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2248_ = stack[0].m_obj;
lean_object* v_____do__lift_2249_ = stack[1].m_obj;
lean_object* v___y_2250_ = stack[2].m_obj;
lean_object* v___y_2251_ = stack[3].m_obj;
lean_object* v___y_2252_ = stack[4].m_obj;
lean_object* v___y_2253_ = stack[5].m_obj;
lean_object* v___y_2254_ = stack[6].m_obj;
lean_object* v_res_2266_;
v_res_2266_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2248_, v_____do__lift_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
stack->m_obj
 = v_res_2266_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3___boxed(lean_object* v___x_2267_, lean_object* v_____do__lift_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_2267_, v_____do__lift_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v_____do__lift_2268_);
return v_res_2275_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(lean_object* v_declName_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; lean_object* v_env_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2279_ = lean_st_ref_get(v___y_2277_);
v_env_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc_ref(v_env_2280_);
lean_dec(v___x_2279_);
v___x_2281_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2280_, v_declName_2276_);
v___x_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2276_ = stack[0].m_obj;
lean_object* v___y_2277_ = stack[1].m_obj;
lean_object* v_res_2283_;
v_res_2283_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2276_, v___y_2277_);
stack->m_obj
 = v_res_2283_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg___boxed(lean_object* v_declName_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2284_, v___y_2285_);
lean_dec(v___y_2285_);
return v_res_2287_;
}
}
lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(lean_object* v_msg_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; lean_object* v_toApplicative_2296_; lean_object* v_toFunctor_2297_; lean_object* v_toSeq_2298_; lean_object* v_toSeqLeft_2299_; lean_object* v_toSeqRight_2300_; lean_object* v___f_2301_; lean_object* v___f_2302_; lean_object* v___f_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_toApplicative_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2344_; 
v___x_2295_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_2296_ = lean_ctor_get(v___x_2295_, 0);
v_toFunctor_2297_ = lean_ctor_get(v_toApplicative_2296_, 0);
v_toSeq_2298_ = lean_ctor_get(v_toApplicative_2296_, 2);
v_toSeqLeft_2299_ = lean_ctor_get(v_toApplicative_2296_, 3);
v_toSeqRight_2300_ = lean_ctor_get(v_toApplicative_2296_, 4);
v___f_2301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_2302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2297_, 2);
v___f_2303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2303_, 0, v_toFunctor_2297_);
v___f_2304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2304_, 0, v_toFunctor_2297_);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___f_2303_);
lean_ctor_set(v___x_2305_, 1, v___f_2304_);
lean_inc(v_toSeqRight_2300_);
v___f_2306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2306_, 0, v_toSeqRight_2300_);
lean_inc(v_toSeqLeft_2299_);
v___f_2307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2307_, 0, v_toSeqLeft_2299_);
lean_inc(v_toSeq_2298_);
v___f_2308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2308_, 0, v_toSeq_2298_);
v___x_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2305_);
lean_ctor_set(v___x_2309_, 1, v___f_2301_);
lean_ctor_set(v___x_2309_, 2, v___f_2308_);
lean_ctor_set(v___x_2309_, 3, v___f_2307_);
lean_ctor_set(v___x_2309_, 4, v___f_2306_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___f_2302_);
v___x_2311_ = l_StateRefT_x27_instMonad___redArg(v___x_2310_);
v_toApplicative_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v___x_2311_, 1);
lean_dec(v_unused_2345_);
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2344_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_toApplicative_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2344_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v_toFunctor_2316_; lean_object* v_toSeq_2317_; lean_object* v_toSeqLeft_2318_; lean_object* v_toSeqRight_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2342_; 
v_toFunctor_2316_ = lean_ctor_get(v_toApplicative_2312_, 0);
v_toSeq_2317_ = lean_ctor_get(v_toApplicative_2312_, 2);
v_toSeqLeft_2318_ = lean_ctor_get(v_toApplicative_2312_, 3);
v_toSeqRight_2319_ = lean_ctor_get(v_toApplicative_2312_, 4);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_toApplicative_2312_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v_toApplicative_2312_, 1);
lean_dec(v_unused_2343_);
v___x_2321_ = v_toApplicative_2312_;
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_toSeqRight_2319_);
lean_inc(v_toSeqLeft_2318_);
lean_inc(v_toSeq_2317_);
lean_inc(v_toFunctor_2316_);
lean_dec(v_toApplicative_2312_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___f_2323_; lean_object* v___f_2324_; lean_object* v___f_2325_; lean_object* v___f_2326_; lean_object* v___x_2327_; lean_object* v___f_2328_; lean_object* v___f_2329_; lean_object* v___f_2330_; lean_object* v___x_2332_; 
v___f_2323_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_2324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_2316_);
v___f_2325_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2325_, 0, v_toFunctor_2316_);
v___f_2326_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2326_, 0, v_toFunctor_2316_);
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___f_2325_);
lean_ctor_set(v___x_2327_, 1, v___f_2326_);
v___f_2328_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2328_, 0, v_toSeqRight_2319_);
v___f_2329_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2329_, 0, v_toSeqLeft_2318_);
v___f_2330_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2330_, 0, v_toSeq_2317_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v___f_2328_);
lean_ctor_set(v___x_2321_, 3, v___f_2329_);
lean_ctor_set(v___x_2321_, 2, v___f_2330_);
lean_ctor_set(v___x_2321_, 1, v___f_2323_);
lean_ctor_set(v___x_2321_, 0, v___x_2327_);
v___x_2332_ = v___x_2321_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___f_2323_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v___f_2330_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v___f_2329_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v___f_2328_);
v___x_2332_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2334_; 
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 1, v___f_2324_);
lean_ctor_set(v___x_2314_, 0, v___x_2332_);
v___x_2334_ = v___x_2314_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2332_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___f_2324_);
v___x_2334_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_23553__overap_2338_; lean_object* v___x_2339_; 
v___x_2335_ = l_StateRefT_x27_instMonad___redArg(v___x_2334_);
v___x_2336_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2337_ = l_instInhabitedOfMonad___redArg(v___x_2335_, v___x_2336_);
v___x_23553__overap_2338_ = lean_panic_fn_borrowed(v___x_2337_, v_msg_2288_);
lean_dec(v___x_2337_);
lean_inc(v___y_2293_);
lean_inc_ref(v___y_2292_);
lean_inc(v___y_2291_);
lean_inc_ref(v___y_2290_);
lean_inc(v___y_2289_);
v___x_2339_ = lean_apply_6(v___x_23553__overap_2338_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, lean_box(0));
return v___x_2339_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2288_ = stack[0].m_obj;
lean_object* v___y_2289_ = stack[1].m_obj;
lean_object* v___y_2290_ = stack[2].m_obj;
lean_object* v___y_2291_ = stack[3].m_obj;
lean_object* v___y_2292_ = stack[4].m_obj;
lean_object* v___y_2293_ = stack[5].m_obj;
lean_object* v_res_2346_;
v_res_2346_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
stack->m_obj
 = v_res_2346_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7___boxed(lean_object* v_msg_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v_msg_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
return v_res_2354_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0(void){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2355_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__0);
v___x_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2358_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
lean_ctor_set(v___x_2361_, 2, v___x_2360_);
lean_ctor_set(v___x_2361_, 3, v___x_2360_);
lean_ctor_set(v___x_2361_, 4, v___x_2359_);
lean_ctor_set(v___x_2361_, 5, v___x_2359_);
lean_ctor_set(v___x_2361_, 6, v___x_2359_);
lean_ctor_set(v___x_2361_, 7, v___x_2359_);
lean_ctor_set(v___x_2361_, 8, v___x_2359_);
lean_ctor_set(v___x_2361_, 9, v___x_2359_);
lean_ctor_set(v___x_2361_, 10, v___x_2359_);
lean_ctor_set(v___x_2361_, 11, v___x_2358_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3(void){
_start:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(32u);
v___x_2363_ = lean_mk_empty_array_with_capacity(v___x_2362_);
v___x_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
return v___x_2364_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4(void){
_start:
{
size_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2365_ = ((size_t)5ULL);
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_unsigned_to_nat(32u);
v___x_2368_ = lean_mk_empty_array_with_capacity(v___x_2367_);
v___x_2369_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__3);
v___x_2370_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v___x_2368_);
lean_ctor_set(v___x_2370_, 2, v___x_2366_);
lean_ctor_set(v___x_2370_, 3, v___x_2366_);
lean_ctor_set_usize(v___x_2370_, 4, v___x_2365_);
return v___x_2370_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2371_ = lean_box(1);
v___x_2372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__4);
v___x_2373_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__1);
v___x_2374_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v___x_2372_);
lean_ctor_set(v___x_2374_, 2, v___x_2371_);
return v___x_2374_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__6));
v___x_2377_ = l_Lean_stringToMessageData(v___x_2376_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__8));
v___x_2380_ = l_Lean_stringToMessageData(v___x_2379_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__10));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__12));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__14));
v___x_2389_ = l_Lean_stringToMessageData(v___x_2388_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__16));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__18));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__20));
v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__22));
v___x_2401_ = l_Lean_stringToMessageData(v___x_2400_);
return v___x_2401_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25(void){
_start:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__24));
v___x_2404_ = l_Lean_stringToMessageData(v___x_2403_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__26));
v___x_2407_ = l_Lean_stringToMessageData(v___x_2406_);
return v___x_2407_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(lean_object* v_msg_2408_, lean_object* v_declHint_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v_env_2414_; uint8_t v___x_2415_; 
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_st_ref_get(v___y_2410_);
v_env_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_env_2414_);
lean_dec(v___x_2413_);
v___x_2415_ = l_Lean_Name_isAnonymous(v_declHint_2409_);
if (v___x_2415_ == 0)
{
uint8_t v_isExporting_2416_; 
v_isExporting_2416_ = lean_ctor_get_uint8(v_env_2414_, sizeof(void*)*13);
if (v_isExporting_2416_ == 0)
{
lean_object* v___x_2417_; 
lean_dec_ref(v_env_2414_);
lean_dec(v_declHint_2409_);
v___x_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_msg_2408_);
return v___x_2417_;
}
else
{
lean_object* v___x_2418_; uint8_t v___x_2419_; 
lean_inc_ref(v_env_2414_);
v___x_2418_ = l_Lean_Environment_setExporting(v_env_2414_, v___x_2415_);
lean_inc(v_declHint_2409_);
lean_inc_ref(v___x_2418_);
v___x_2419_ = l_Lean_Environment_contains(v___x_2418_, v_declHint_2409_, v_isExporting_2416_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v___x_2418_);
lean_dec_ref(v_env_2414_);
lean_dec(v_declHint_2409_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v_msg_2408_);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v_c_2426_; lean_object* v___x_2427_; 
v___x_2421_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__2);
v___x_2422_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__5);
v___x_2423_ = l_Lean_Options_empty;
v___x_2424_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2418_);
lean_ctor_set(v___x_2424_, 1, v___x_2421_);
lean_ctor_set(v___x_2424_, 2, v___x_2422_);
lean_ctor_set(v___x_2424_, 3, v___x_2423_);
lean_inc(v_declHint_2409_);
v___x_2425_ = l_Lean_MessageData_ofConstName(v_declHint_2409_, v___x_2415_);
v_c_2426_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2426_, 0, v___x_2424_);
lean_ctor_set(v_c_2426_, 1, v___x_2425_);
v___x_2427_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2414_, v_declHint_2409_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
lean_dec_ref(v_env_2414_);
lean_dec(v_declHint_2409_);
v___x_2428_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v_c_2426_);
v___x_2430_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__9);
v___x_2431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = l_Lean_MessageData_note(v___x_2431_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v_msg_2408_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
else
{
lean_object* v_val_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2491_; 
v_val_2435_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2437_ = v___x_2427_;
v_isShared_2438_ = v_isSharedCheck_2491_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_val_2435_);
lean_dec(v___x_2427_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2491_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v_modules_2440_; lean_object* v_moduleNames_2441_; lean_object* v_mod_2442_; uint8_t v___y_2444_; uint8_t v___x_2474_; 
v___x_2439_ = l_Lean_Environment_header(v_env_2414_);
lean_dec_ref(v_env_2414_);
v_modules_2440_ = lean_ctor_get(v___x_2439_, 3);
lean_inc_ref(v_modules_2440_);
v_moduleNames_2441_ = lean_ctor_get(v___x_2439_, 4);
lean_inc_ref(v_moduleNames_2441_);
lean_dec_ref(v___x_2439_);
v_mod_2442_ = lean_array_get(v___x_2412_, v_moduleNames_2441_, v_val_2435_);
lean_dec_ref(v_moduleNames_2441_);
v___x_2474_ = l_Lean_isPrivateName(v_declHint_2409_);
lean_dec(v_declHint_2409_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = lean_array_get_size(v_modules_2440_);
v___x_2476_ = lean_nat_dec_lt(v_val_2435_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_dec_ref(v_modules_2440_);
lean_dec(v_val_2435_);
v___y_2444_ = v___x_2474_;
goto v___jp_2443_;
}
else
{
lean_object* v___x_2477_; lean_object* v_toImport_2478_; uint8_t v_isExported_2479_; 
v___x_2477_ = lean_array_fget(v_modules_2440_, v_val_2435_);
lean_dec(v_val_2435_);
lean_dec_ref(v_modules_2440_);
v_toImport_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc_ref(v_toImport_2478_);
lean_dec(v___x_2477_);
v_isExported_2479_ = lean_ctor_get_uint8(v_toImport_2478_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2478_);
v___y_2444_ = v_isExported_2479_;
goto v___jp_2443_;
}
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
lean_dec_ref(v_modules_2440_);
lean_del_object(v___x_2437_);
lean_dec(v_val_2435_);
v___x_2480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__7);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v_c_2426_);
v___x_2482_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__25);
v___x_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2483_, 0, v___x_2481_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
v___x_2484_ = l_Lean_MessageData_ofName(v_mod_2442_);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__27);
v___x_2487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = l_Lean_MessageData_note(v___x_2487_);
v___x_2489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_msg_2408_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2489_);
return v___x_2490_;
}
v___jp_2443_:
{
if (v___y_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2445_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__11);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v_c_2426_);
v___x_2447_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__13);
v___x_2448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = l_Lean_MessageData_ofName(v_mod_2442_);
v___x_2450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2450_, 0, v___x_2448_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__15);
v___x_2452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = l_Lean_MessageData_note(v___x_2452_);
v___x_2454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2454_, 0, v_msg_2408_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2454_);
v___x_2456_ = v___x_2437_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2458_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__17);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
lean_ctor_set(v___x_2459_, 1, v_c_2426_);
v___x_2460_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__19);
v___x_2461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = l_Lean_MessageData_ofName(v_mod_2442_);
lean_inc_ref(v___x_2462_);
v___x_2463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__21);
v___x_2465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2465_, 0, v___x_2463_);
lean_ctor_set(v___x_2465_, 1, v___x_2464_);
v___x_2466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2465_);
lean_ctor_set(v___x_2466_, 1, v___x_2462_);
v___x_2467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___closed__23);
v___x_2468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = l_Lean_MessageData_note(v___x_2468_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_msg_2408_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2470_);
v___x_2472_ = v___x_2437_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
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
lean_object* v___x_2492_; 
lean_dec_ref(v_env_2414_);
lean_dec(v_declHint_2409_);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_msg_2408_);
return v___x_2492_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2408_ = stack[0].m_obj;
lean_object* v_declHint_2409_ = stack[1].m_obj;
lean_object* v___y_2410_ = stack[2].m_obj;
lean_object* v_res_2493_;
v_res_2493_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2408_, v_declHint_2409_, v___y_2410_);
stack->m_obj
 = v_res_2493_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg___boxed(lean_object* v_msg_2494_, lean_object* v_declHint_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2494_, v_declHint_2495_, v___y_2496_);
lean_dec(v___y_2496_);
return v_res_2498_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(lean_object* v_msg_2499_, lean_object* v_declHint_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2517_; 
v___x_2507_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_2499_, v_declHint_2500_, v___y_2505_);
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2517_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2517_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2515_; 
v___x_2512_ = l_Lean_unknownIdentifierMessageTag;
v___x_2513_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v_a_2508_);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2513_);
v___x_2515_ = v___x_2510_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2499_ = stack[0].m_obj;
lean_object* v_declHint_2500_ = stack[1].m_obj;
lean_object* v___y_2501_ = stack[2].m_obj;
lean_object* v___y_2502_ = stack[3].m_obj;
lean_object* v___y_2503_ = stack[4].m_obj;
lean_object* v___y_2504_ = stack[5].m_obj;
lean_object* v___y_2505_ = stack[6].m_obj;
lean_object* v_res_2518_;
v_res_2518_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2499_, v_declHint_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
stack->m_obj
 = v_res_2518_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18___boxed(lean_object* v_msg_2519_, lean_object* v_declHint_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2519_, v_declHint_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
return v_res_2527_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_ref_2534_; lean_object* v___x_2535_; lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2544_; 
v_ref_2534_ = lean_ctor_get(v___y_2531_, 2);
v___x_2535_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0_spec__0(v_msg_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2544_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2542_; 
lean_inc(v_ref_2534_);
v___x_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2540_, 0, v_ref_2534_);
lean_ctor_set(v___x_2540_, 1, v_a_2536_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set_tag(v___x_2538_, 1);
lean_ctor_set(v___x_2538_, 0, v___x_2540_);
v___x_2542_ = v___x_2538_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2528_ = stack[0].m_obj;
lean_object* v___y_2529_ = stack[1].m_obj;
lean_object* v___y_2530_ = stack[2].m_obj;
lean_object* v___y_2531_ = stack[3].m_obj;
lean_object* v___y_2532_ = stack[4].m_obj;
lean_object* v_res_2545_;
v_res_2545_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
stack->m_obj
 = v_res_2545_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg___boxed(lean_object* v_msg_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
return v_res_2552_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(lean_object* v_ref_2553_, lean_object* v_msg_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_toCold_2561_; lean_object* v_currRecDepth_2562_; lean_object* v_ref_2563_; uint16_t v_optionFlags_2564_; uint8_t v_suppressElabErrors_2565_; uint8_t v_isRecordingDeps_2566_; lean_object* v_ref_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_toCold_2561_ = lean_ctor_get(v___y_2558_, 0);
v_currRecDepth_2562_ = lean_ctor_get(v___y_2558_, 1);
v_ref_2563_ = lean_ctor_get(v___y_2558_, 2);
v_optionFlags_2564_ = lean_ctor_get_uint16(v___y_2558_, sizeof(void*)*3);
v_suppressElabErrors_2565_ = lean_ctor_get_uint8(v___y_2558_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2566_ = lean_ctor_get_uint8(v___y_2558_, sizeof(void*)*3 + 3);
v_ref_2567_ = l_Lean_replaceRef(v_ref_2553_, v_ref_2563_);
lean_inc(v_currRecDepth_2562_);
lean_inc_ref(v_toCold_2561_);
v___x_2568_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2568_, 0, v_toCold_2561_);
lean_ctor_set(v___x_2568_, 1, v_currRecDepth_2562_);
lean_ctor_set(v___x_2568_, 2, v_ref_2567_);
lean_ctor_set_uint16(v___x_2568_, sizeof(void*)*3, v_optionFlags_2564_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*3 + 2, v_suppressElabErrors_2565_);
lean_ctor_set_uint8(v___x_2568_, sizeof(void*)*3 + 3, v_isRecordingDeps_2566_);
v___x_2569_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_2554_, v___y_2556_, v___y_2557_, v___x_2568_, v___y_2559_);
lean_dec_ref_known(v___x_2568_, 3);
return v___x_2569_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2553_ = stack[0].m_obj;
lean_object* v_msg_2554_ = stack[1].m_obj;
lean_object* v___y_2555_ = stack[2].m_obj;
lean_object* v___y_2556_ = stack[3].m_obj;
lean_object* v___y_2557_ = stack[4].m_obj;
lean_object* v___y_2558_ = stack[5].m_obj;
lean_object* v___y_2559_ = stack[6].m_obj;
lean_object* v_res_2570_;
v_res_2570_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2553_, v_msg_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
stack->m_obj
 = v_res_2570_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_ref_2571_, lean_object* v_msg_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2571_, v_msg_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec(v_ref_2571_);
return v_res_2579_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(lean_object* v_ref_2580_, lean_object* v_msg_2581_, lean_object* v_declHint_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v_a_2590_; lean_object* v___x_2591_; 
v___x_2589_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18(v_msg_2581_, v_declHint_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_a_2590_);
lean_dec_ref(v___x_2589_);
v___x_2591_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_2580_, v_a_2590_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2591_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2580_ = stack[0].m_obj;
lean_object* v_msg_2581_ = stack[1].m_obj;
lean_object* v_declHint_2582_ = stack[2].m_obj;
lean_object* v___y_2583_ = stack[3].m_obj;
lean_object* v___y_2584_ = stack[4].m_obj;
lean_object* v___y_2585_ = stack[5].m_obj;
lean_object* v___y_2586_ = stack[6].m_obj;
lean_object* v___y_2587_ = stack[7].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2580_, v_msg_2581_, v_declHint_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg___boxed(lean_object* v_ref_2593_, lean_object* v_msg_2594_, lean_object* v_declHint_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2593_, v_msg_2594_, v_declHint_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec(v_ref_2593_);
return v_res_2602_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__0));
v___x_2605_ = l_Lean_stringToMessageData(v___x_2604_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__2));
v___x_2608_ = l_Lean_stringToMessageData(v___x_2607_);
return v___x_2608_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(lean_object* v_ref_2609_, lean_object* v_constName_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; uint8_t v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2617_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__1);
v___x_2618_ = 0;
lean_inc(v_constName_2610_);
v___x_2619_ = l_Lean_MessageData_ofConstName(v_constName_2610_, v___x_2618_);
v___x_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2617_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___closed__3);
v___x_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2620_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_2609_, v___x_2622_, v_constName_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2623_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2609_ = stack[0].m_obj;
lean_object* v_constName_2610_ = stack[1].m_obj;
lean_object* v___y_2611_ = stack[2].m_obj;
lean_object* v___y_2612_ = stack[3].m_obj;
lean_object* v___y_2613_ = stack[4].m_obj;
lean_object* v___y_2614_ = stack[5].m_obj;
lean_object* v___y_2615_ = stack[6].m_obj;
lean_object* v_res_2624_;
v_res_2624_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2609_, v_constName_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
stack->m_obj
 = v_res_2624_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg___boxed(lean_object* v_ref_2625_, lean_object* v_constName_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2625_, v_constName_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v_ref_2625_);
return v_res_2633_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(lean_object* v_constName_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_ref_2641_; lean_object* v___x_2642_; 
v_ref_2641_ = lean_ctor_get(v___y_2638_, 2);
v___x_2642_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_2641_, v_constName_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2642_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2634_ = stack[0].m_obj;
lean_object* v___y_2635_ = stack[1].m_obj;
lean_object* v___y_2636_ = stack[2].m_obj;
lean_object* v___y_2637_ = stack[3].m_obj;
lean_object* v___y_2638_ = stack[4].m_obj;
lean_object* v___y_2639_ = stack[5].m_obj;
lean_object* v_res_2643_;
v_res_2643_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
stack->m_obj
 = v_res_2643_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_constName_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
return v_res_2651_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(lean_object* v_constName_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; lean_object* v_env_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v___x_2659_ = lean_st_ref_get(v___y_2657_);
v_env_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_ref(v_env_2660_);
lean_dec(v___x_2659_);
v___x_2661_ = 0;
lean_inc(v_constName_2652_);
v___x_2662_ = l_Lean_Environment_find_x3f(v_env_2660_, v_constName_2652_, v___x_2661_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
return v___x_2663_;
}
else
{
lean_object* v_val_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec(v_constName_2652_);
v_val_2664_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2662_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_val_2664_);
lean_dec(v___x_2662_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set_tag(v___x_2666_, 0);
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_val_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2652_ = stack[0].m_obj;
lean_object* v___y_2653_ = stack[1].m_obj;
lean_object* v___y_2654_ = stack[2].m_obj;
lean_object* v___y_2655_ = stack[3].m_obj;
lean_object* v___y_2656_ = stack[4].m_obj;
lean_object* v___y_2657_ = stack[5].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6___boxed(lean_object* v_constName_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_constName_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
return v_res_2680_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2684_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__2));
v___x_2685_ = lean_unsigned_to_nat(53u);
v___x_2686_ = lean_unsigned_to_nat(62u);
v___x_2687_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__1));
v___x_2688_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__0));
v___x_2689_ = l_mkPanicMessageWithDecl(v___x_2688_, v___x_2687_, v___x_2686_, v___x_2685_, v___x_2684_);
return v___x_2689_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(size_t v_sz_2690_, size_t v_i_2691_, lean_object* v_bs_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v___x_2699_; 
v___x_2699_ = lean_usize_dec_lt(v_i_2691_, v_sz_2690_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_bs_2692_);
return v___x_2700_;
}
else
{
lean_object* v_v_2701_; lean_object* v___x_2702_; lean_object* v_bs_x27_2703_; lean_object* v_a_2705_; lean_object* v___x_2710_; 
v_v_2701_ = lean_array_uget(v_bs_2692_, v_i_2691_);
v___x_2702_ = lean_unsigned_to_nat(0u);
v_bs_x27_2703_ = lean_array_uset(v_bs_2692_, v_i_2691_, v___x_2702_);
v___x_2710_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_v_2701_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
if (lean_obj_tag(v_a_2711_) == 6)
{
lean_object* v_val_2712_; lean_object* v_numFields_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; 
v_val_2712_ = lean_ctor_get(v_a_2711_, 0);
lean_inc_ref(v_val_2712_);
lean_dec_ref_known(v_a_2711_, 1);
v_numFields_2713_ = lean_ctor_get(v_val_2712_, 4);
lean_inc(v_numFields_2713_);
lean_dec_ref(v_val_2712_);
v___x_2714_ = 0;
v___x_2715_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2715_, 0, v_numFields_2713_);
lean_ctor_set(v___x_2715_, 1, v___x_2702_);
lean_ctor_set_uint8(v___x_2715_, sizeof(void*)*2, v___x_2714_);
v_a_2705_ = v___x_2715_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec(v_a_2711_);
v___x_2716_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___closed__3);
v___x_2717_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__7(v___x_2716_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v_a_2705_ = v_a_2718_;
goto v___jp_2704_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec_ref(v_bs_x27_2703_);
v_a_2719_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2717_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2717_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2724_; 
if (v_isShared_2722_ == 0)
{
v___x_2724_ = v___x_2721_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_a_2719_);
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
}
else
{
lean_object* v_a_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2734_; 
lean_dec_ref(v_bs_x27_2703_);
v_a_2727_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2729_ = v___x_2710_;
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_a_2727_);
lean_dec(v___x_2710_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2734_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2732_; 
if (v_isShared_2730_ == 0)
{
v___x_2732_ = v___x_2729_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_a_2727_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
v___jp_2704_:
{
size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2691_, v___x_2706_);
v___x_2708_ = lean_array_uset(v_bs_x27_2703_, v_i_2691_, v_a_2705_);
v_i_2691_ = v___x_2707_;
v_bs_2692_ = v___x_2708_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2690_ = stack[0].m_num;
size_t v_i_2691_ = stack[1].m_num;
lean_object* v_bs_2692_ = stack[2].m_obj;
lean_object* v___y_2693_ = stack[3].m_obj;
lean_object* v___y_2694_ = stack[4].m_obj;
lean_object* v___y_2695_ = stack[5].m_obj;
lean_object* v___y_2696_ = stack[6].m_obj;
lean_object* v___y_2697_ = stack[7].m_obj;
lean_object* v_res_2735_;
v_res_2735_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2690_, v_i_2691_, v_bs_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
stack->m_obj
 = v_res_2735_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9___boxed(lean_object* v_sz_2736_, lean_object* v_i_2737_, lean_object* v_bs_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
size_t v_sz_boxed_2745_; size_t v_i_boxed_2746_; lean_object* v_res_2747_; 
v_sz_boxed_2745_ = lean_unbox_usize(v_sz_2736_);
lean_dec(v_sz_2736_);
v_i_boxed_2746_ = lean_unbox_usize(v_i_2737_);
lean_dec(v_i_2737_);
v_res_2747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_boxed_2745_, v_i_boxed_2746_, v_bs_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
return v_res_2747_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2748_ = lean_box(0);
v___x_2749_ = lean_unsigned_to_nat(16u);
v___x_2750_ = lean_mk_array(v___x_2749_, v___x_2748_);
return v___x_2750_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2751_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__0);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
lean_ctor_set(v___x_2753_, 1, v___x_2751_);
return v___x_2753_;
}
}
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(lean_object* v_e_2756_, uint8_t v_alsoCasesOn_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
uint8_t v___x_2767_; 
v___x_2767_ = l_Lean_Expr_isApp(v_e_2756_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_dec_ref(v_e_2756_);
v___x_2768_ = lean_box(0);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Expr_getAppFn(v_e_2756_);
if (lean_obj_tag(v___x_2770_) == 4)
{
lean_object* v_declName_2771_; lean_object* v_us_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2927_; 
v_declName_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc_n(v_declName_2771_, 2);
v_us_2772_ = lean_ctor_get(v___x_2770_, 1);
lean_inc(v_us_2772_);
lean_dec_ref_known(v___x_2770_, 2);
v___x_2773_ = l_Lean_instInhabitedExpr;
v___x_2774_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_2771_, v___y_2762_);
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2777_ = v___x_2774_;
v_isShared_2778_ = v_isSharedCheck_2927_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2927_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
if (lean_obj_tag(v_a_2775_) == 1)
{
lean_object* v_val_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2820_; 
v_val_2779_ = lean_ctor_get(v_a_2775_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_a_2775_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2781_ = v_a_2775_;
v_isShared_2782_ = v_isSharedCheck_2820_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_val_2779_);
lean_dec(v_a_2775_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2820_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_dummy_2783_; lean_object* v_nargs_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v_args_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_dummy_2783_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_2784_ = l_Lean_Expr_getAppNumArgs(v_e_2756_);
lean_inc(v_nargs_2784_);
v___x_2785_ = lean_mk_array(v_nargs_2784_, v_dummy_2783_);
v___x_2786_ = lean_unsigned_to_nat(1u);
v___x_2787_ = lean_nat_sub(v_nargs_2784_, v___x_2786_);
lean_dec(v_nargs_2784_);
v_args_2788_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2756_, v___x_2785_, v___x_2787_);
v___x_2789_ = lean_array_get_size(v_args_2788_);
v___x_2790_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2779_);
v___x_2791_ = lean_nat_dec_lt(v___x_2789_, v___x_2790_);
lean_dec(v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v_numParams_2792_; lean_object* v_numDiscrs_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v_numParams_2792_ = lean_ctor_get(v_val_2779_, 0);
v_numDiscrs_2793_ = lean_ctor_get(v_val_2779_, 1);
v___x_2794_ = lean_array_mk(v_us_2772_);
v___x_2795_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2792_);
v___x_2796_ = l_Array_extract___redArg(v_args_2788_, v___x_2795_, v_numParams_2792_);
v___x_2797_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2779_);
v___x_2798_ = lean_array_get(v___x_2773_, v_args_2788_, v___x_2797_);
lean_dec(v___x_2797_);
v___x_2799_ = lean_nat_add(v_numParams_2792_, v___x_2786_);
v___x_2800_ = lean_nat_add(v___x_2799_, v_numDiscrs_2793_);
lean_inc(v___x_2800_);
lean_inc_ref_n(v_args_2788_, 2);
v___x_2801_ = l_Array_toSubarray___redArg(v_args_2788_, v___x_2799_, v___x_2800_);
v___x_2802_ = l_Subarray_copy___redArg(v___x_2801_);
v___x_2803_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2779_);
v___x_2804_ = lean_nat_add(v___x_2800_, v___x_2803_);
lean_dec(v___x_2803_);
lean_inc(v___x_2804_);
v___x_2805_ = l_Array_toSubarray___redArg(v_args_2788_, v___x_2800_, v___x_2804_);
v___x_2806_ = l_Subarray_copy___redArg(v___x_2805_);
v___x_2807_ = l_Array_toSubarray___redArg(v_args_2788_, v___x_2804_, v___x_2789_);
v___x_2808_ = l_Subarray_copy___redArg(v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2809_, 0, v_val_2779_);
lean_ctor_set(v___x_2809_, 1, v_declName_2771_);
lean_ctor_set(v___x_2809_, 2, v___x_2794_);
lean_ctor_set(v___x_2809_, 3, v___x_2796_);
lean_ctor_set(v___x_2809_, 4, v___x_2798_);
lean_ctor_set(v___x_2809_, 5, v___x_2802_);
lean_ctor_set(v___x_2809_, 6, v___x_2806_);
lean_ctor_set(v___x_2809_, 7, v___x_2808_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2809_);
v___x_2811_ = v___x_2781_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2811_);
v___x_2813_ = v___x_2777_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
lean_dec_ref(v_args_2788_);
lean_del_object(v___x_2781_);
lean_dec(v_val_2779_);
lean_dec(v_us_2772_);
lean_dec(v_declName_2771_);
v___x_2816_ = lean_box(0);
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v___x_2816_);
v___x_2818_ = v___x_2777_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v___x_2816_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v___x_2821_; 
lean_del_object(v___x_2777_);
lean_dec(v_a_2775_);
v___x_2821_ = lean_st_ref_get(v___y_2762_);
if (v_alsoCasesOn_2757_ == 0)
{
lean_dec(v___x_2821_);
lean_dec(v_us_2772_);
lean_dec(v_declName_2771_);
lean_dec_ref(v_e_2756_);
goto v___jp_2764_;
}
else
{
lean_object* v_env_2822_; uint8_t v___x_2823_; 
v_env_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc_ref(v_env_2822_);
lean_dec(v___x_2821_);
lean_inc(v_declName_2771_);
v___x_2823_ = l_Lean_isCasesOnRecursor(v_env_2822_, v_declName_2771_);
if (v___x_2823_ == 0)
{
lean_dec(v_us_2772_);
lean_dec(v_declName_2771_);
lean_dec_ref(v_e_2756_);
goto v___jp_2764_;
}
else
{
lean_object* v_indName_2824_; lean_object* v___x_2825_; 
v_indName_2824_ = l_Lean_Name_getPrefix(v_declName_2771_);
v___x_2825_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6(v_indName_2824_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2918_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2828_ = v___x_2825_;
v_isShared_2829_ = v_isSharedCheck_2918_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2918_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
if (lean_obj_tag(v_a_2826_) == 5)
{
lean_object* v_val_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2913_; 
v_val_2830_ = lean_ctor_get(v_a_2826_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_a_2826_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2832_ = v_a_2826_;
v_isShared_2833_ = v_isSharedCheck_2913_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_val_2830_);
lean_dec(v_a_2826_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2913_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v_toConstantVal_2834_; lean_object* v_numParams_2835_; lean_object* v_numIndices_2836_; lean_object* v_ctors_2837_; lean_object* v_nargs_2838_; lean_object* v_dummy_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v_args_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_toConstantVal_2834_ = lean_ctor_get(v_val_2830_, 0);
lean_inc_ref(v_toConstantVal_2834_);
v_numParams_2835_ = lean_ctor_get(v_val_2830_, 1);
lean_inc(v_numParams_2835_);
v_numIndices_2836_ = lean_ctor_get(v_val_2830_, 2);
lean_inc(v_numIndices_2836_);
v_ctors_2837_ = lean_ctor_get(v_val_2830_, 4);
lean_inc(v_ctors_2837_);
v_nargs_2838_ = l_Lean_Expr_getAppNumArgs(v_e_2756_);
v_dummy_2839_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
lean_inc(v_nargs_2838_);
v___x_2840_ = lean_mk_array(v_nargs_2838_, v_dummy_2839_);
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_nat_sub(v_nargs_2838_, v___x_2841_);
lean_dec(v_nargs_2838_);
v_args_2843_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2756_, v___x_2840_, v___x_2842_);
v___x_2844_ = lean_nat_add(v_numParams_2835_, v___x_2841_);
v___x_2845_ = lean_nat_add(v___x_2844_, v_numIndices_2836_);
v___x_2846_ = lean_nat_add(v___x_2845_, v___x_2841_);
lean_dec(v___x_2845_);
v___x_2847_ = l_Lean_InductiveVal_numCtors(v_val_2830_);
lean_dec_ref(v_val_2830_);
v___x_2848_ = lean_nat_add(v___x_2846_, v___x_2847_);
lean_dec(v___x_2847_);
v___x_2849_ = lean_array_get_size(v_args_2843_);
v___x_2850_ = lean_nat_dec_le(v___x_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
lean_dec(v___x_2848_);
lean_dec(v___x_2846_);
lean_dec(v___x_2844_);
lean_dec_ref(v_args_2843_);
lean_dec(v_ctors_2837_);
lean_dec(v_numIndices_2836_);
lean_dec(v_numParams_2835_);
lean_dec_ref(v_toConstantVal_2834_);
lean_del_object(v___x_2832_);
lean_dec(v_us_2772_);
lean_dec(v_declName_2771_);
v___x_2851_ = lean_box(0);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2851_);
v___x_2853_ = v___x_2828_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
else
{
lean_object* v___x_2855_; lean_object* v_params_2856_; lean_object* v_motive_2857_; lean_object* v_discrs_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v_discrInfos_2861_; lean_object* v_alts_2862_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v_lower_2904_; lean_object* v_upper_2905_; uint8_t v___x_2912_; 
lean_del_object(v___x_2828_);
v___x_2855_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2835_);
lean_inc_ref_n(v_args_2843_, 3);
v_params_2856_ = l_Array_toSubarray___redArg(v_args_2843_, v___x_2855_, v_numParams_2835_);
v_motive_2857_ = lean_array_get(v___x_2773_, v_args_2843_, v_numParams_2835_);
lean_dec(v_numParams_2835_);
lean_inc(v___x_2846_);
v_discrs_2858_ = l_Array_toSubarray___redArg(v_args_2843_, v___x_2844_, v___x_2846_);
v___x_2859_ = lean_nat_add(v_numIndices_2836_, v___x_2841_);
lean_dec(v_numIndices_2836_);
v___x_2860_ = lean_box(0);
v_discrInfos_2861_ = lean_mk_array(v___x_2859_, v___x_2860_);
lean_inc(v___x_2848_);
v_alts_2862_ = l_Array_toSubarray___redArg(v_args_2843_, v___x_2846_, v___x_2848_);
v___x_2912_ = lean_nat_dec_le(v___x_2848_, v___x_2855_);
if (v___x_2912_ == 0)
{
v_lower_2904_ = v___x_2848_;
v_upper_2905_ = v___x_2849_;
goto v___jp_2903_;
}
else
{
lean_dec(v___x_2848_);
v_lower_2904_ = v___x_2855_;
v_upper_2905_ = v___x_2849_;
goto v___jp_2903_;
}
v___jp_2863_:
{
lean_object* v___x_2866_; size_t v_sz_2867_; size_t v___x_2868_; lean_object* v___x_2869_; 
v___x_2866_ = lean_array_mk(v_ctors_2837_);
v_sz_2867_ = lean_array_size(v___x_2866_);
v___x_2868_ = ((size_t)0ULL);
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__9(v_sz_2867_, v___x_2868_, v___x_2866_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2894_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2894_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2894_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_start_2874_; lean_object* v_stop_2875_; lean_object* v_start_2876_; lean_object* v_stop_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v_start_2874_ = lean_ctor_get(v_params_2856_, 1);
v_stop_2875_ = lean_ctor_get(v_params_2856_, 2);
v_start_2876_ = lean_ctor_get(v_discrs_2858_, 1);
v_stop_2877_ = lean_ctor_get(v_discrs_2858_, 2);
v___x_2878_ = lean_nat_sub(v_stop_2875_, v_start_2874_);
v___x_2879_ = lean_nat_sub(v_stop_2877_, v_start_2876_);
v___x_2880_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__1);
v___x_2881_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2878_);
lean_ctor_set(v___x_2881_, 1, v___x_2879_);
lean_ctor_set(v___x_2881_, 2, v_a_2870_);
lean_ctor_set(v___x_2881_, 3, v___y_2865_);
lean_ctor_set(v___x_2881_, 4, v_discrInfos_2861_);
lean_ctor_set(v___x_2881_, 5, v___x_2880_);
v___x_2882_ = lean_array_mk(v_us_2772_);
v___x_2883_ = l_Subarray_copy___redArg(v_params_2856_);
v___x_2884_ = l_Subarray_copy___redArg(v_discrs_2858_);
v___x_2885_ = l_Subarray_copy___redArg(v_alts_2862_);
v___x_2886_ = l_Subarray_copy___redArg(v___y_2864_);
v___x_2887_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2881_);
lean_ctor_set(v___x_2887_, 1, v_declName_2771_);
lean_ctor_set(v___x_2887_, 2, v___x_2882_);
lean_ctor_set(v___x_2887_, 3, v___x_2883_);
lean_ctor_set(v___x_2887_, 4, v_motive_2857_);
lean_ctor_set(v___x_2887_, 5, v___x_2884_);
lean_ctor_set(v___x_2887_, 6, v___x_2885_);
lean_ctor_set(v___x_2887_, 7, v___x_2886_);
if (v_isShared_2833_ == 0)
{
lean_ctor_set_tag(v___x_2832_, 1);
lean_ctor_set(v___x_2832_, 0, v___x_2887_);
v___x_2889_ = v___x_2832_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2891_; 
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v___x_2889_);
v___x_2891_ = v___x_2872_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v___x_2889_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_alts_2862_);
lean_dec_ref(v_discrInfos_2861_);
lean_dec_ref(v_discrs_2858_);
lean_dec(v_motive_2857_);
lean_dec_ref(v_params_2856_);
lean_del_object(v___x_2832_);
lean_dec(v_us_2772_);
lean_dec(v_declName_2771_);
v_a_2895_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2869_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2869_);
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
v___jp_2903_:
{
lean_object* v_levelParams_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_levelParams_2906_ = lean_ctor_get(v_toConstantVal_2834_, 1);
lean_inc(v_levelParams_2906_);
lean_dec_ref(v_toConstantVal_2834_);
v___x_2907_ = l_Array_toSubarray___redArg(v_args_2843_, v_lower_2904_, v_upper_2905_);
v___x_2908_ = l_List_lengthTR___redArg(v_levelParams_2906_);
lean_dec(v_levelParams_2906_);
v___x_2909_ = l_List_lengthTR___redArg(v_us_2772_);
v___x_2910_ = lean_nat_dec_eq(v___x_2908_, v___x_2909_);
lean_dec(v___x_2909_);
lean_dec(v___x_2908_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___closed__2));
v___y_2864_ = v___x_2907_;
v___y_2865_ = v___x_2911_;
goto v___jp_2863_;
}
else
{
v___y_2864_ = v___x_2907_;
v___y_2865_ = v___x_2860_;
goto v___jp_2863_;
}
}
}
}
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2916_; 
lean_dec(v_a_2826_);
lean_dec(v_us_2772_);
lean_dec(v_declName_2771_);
lean_dec_ref(v_e_2756_);
v___x_2914_ = lean_box(0);
if (v_isShared_2829_ == 0)
{
lean_ctor_set(v___x_2828_, 0, v___x_2914_);
v___x_2916_ = v___x_2828_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_us_2772_);
lean_dec(v_declName_2771_);
lean_dec_ref(v_e_2756_);
v_a_2919_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2825_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2825_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
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
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_e_2756_);
goto v___jp_2764_;
}
}
v___jp_2764_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_box(0);
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
return v___x_2766_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2756_ = stack[0].m_obj;
uint8_t v_alsoCasesOn_2757_ = stack[1].m_num;
lean_object* v___y_2758_ = stack[2].m_obj;
lean_object* v___y_2759_ = stack[3].m_obj;
lean_object* v___y_2760_ = stack[4].m_obj;
lean_object* v___y_2761_ = stack[5].m_obj;
lean_object* v___y_2762_ = stack[6].m_obj;
lean_object* v_res_2928_;
v_res_2928_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2756_, v_alsoCasesOn_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
stack->m_obj
 = v_res_2928_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5___boxed(lean_object* v_e_2929_, lean_object* v_alsoCasesOn_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2937_; lean_object* v_res_2938_; 
v_alsoCasesOn_boxed_2937_ = lean_unbox(v_alsoCasesOn_2930_);
v_res_2938_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_2929_, v_alsoCasesOn_boxed_2937_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
if (lean_obj_tag(v_a_2939_) == 0)
{
lean_object* v___x_2941_; 
v___x_2941_ = l_List_reverse___redArg(v_a_2940_);
return v___x_2941_;
}
else
{
lean_object* v_head_2942_; lean_object* v_tail_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2952_; 
v_head_2942_ = lean_ctor_get(v_a_2939_, 0);
v_tail_2943_ = lean_ctor_get(v_a_2939_, 1);
v_isSharedCheck_2952_ = !lean_is_exclusive(v_a_2939_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2945_ = v_a_2939_;
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_tail_2943_);
lean_inc(v_head_2942_);
lean_dec(v_a_2939_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2952_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2947_; lean_object* v___x_2949_; 
v___x_2947_ = l_Lean_MessageData_ofExpr(v_head_2942_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v_a_2940_);
lean_ctor_set(v___x_2945_, 0, v___x_2947_);
v___x_2949_ = v___x_2945_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v_a_2940_);
v___x_2949_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
v_a_2939_ = v_tail_2943_;
v_a_2940_ = v___x_2949_;
goto _start;
}
}
}
}
}
uint8_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(lean_object* v_x_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v_fnName_2955_; uint8_t v___x_2956_; 
v_fnName_2955_ = lean_ctor_get(v_x_2954_, 0);
v___x_2956_ = l_Lean_Expr_isConstOf(v_x_2953_, v_fnName_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2953_ = stack[0].m_obj;
lean_object* v_x_2954_ = stack[1].m_obj;
uint8_t v_res_2957_;
v_res_2957_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2953_, v_x_2954_);
stack->m_num = v_res_2957_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed(lean_object* v_x_2958_, lean_object* v_x_2959_){
_start:
{
uint8_t v_res_2960_; lean_object* v_r_2961_; 
v_res_2960_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0(v_x_2958_, v_x_2959_);
lean_dec_ref(v_x_2959_);
lean_dec_ref(v_x_2958_);
v_r_2961_ = lean_box(v_res_2960_);
return v_r_2961_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(lean_object* v_name_2962_, lean_object* v_type_2963_, lean_object* v_val_2964_, lean_object* v_k_2965_, uint8_t v_nondep_2966_, uint8_t v_kind_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___f_2974_; lean_object* v___x_2975_; 
lean_inc(v___y_2968_);
v___f_2974_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2974_, 0, v_k_2965_);
lean_closure_set(v___f_2974_, 1, v___y_2968_);
v___x_2975_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2962_, v_type_2963_, v_val_2964_, v___f_2974_, v_nondep_2966_, v_kind_2967_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2975_) == 0)
{
return v___x_2975_;
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2962_ = stack[0].m_obj;
lean_object* v_type_2963_ = stack[1].m_obj;
lean_object* v_val_2964_ = stack[2].m_obj;
lean_object* v_k_2965_ = stack[3].m_obj;
uint8_t v_nondep_2966_ = stack[4].m_num;
uint8_t v_kind_2967_ = stack[5].m_num;
lean_object* v___y_2968_ = stack[6].m_obj;
lean_object* v___y_2969_ = stack[7].m_obj;
lean_object* v___y_2970_ = stack[8].m_obj;
lean_object* v___y_2971_ = stack[9].m_obj;
lean_object* v___y_2972_ = stack[10].m_obj;
lean_object* v_res_2984_;
v_res_2984_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2962_, v_type_2963_, v_val_2964_, v_k_2965_, v_nondep_2966_, v_kind_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
stack->m_obj
 = v_res_2984_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg___boxed(lean_object* v_name_2985_, lean_object* v_type_2986_, lean_object* v_val_2987_, lean_object* v_k_2988_, lean_object* v_nondep_2989_, lean_object* v_kind_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
uint8_t v_nondep_boxed_2997_; uint8_t v_kind_boxed_2998_; lean_object* v_res_2999_; 
v_nondep_boxed_2997_ = lean_unbox(v_nondep_2989_);
v_kind_boxed_2998_ = lean_unbox(v_kind_2990_);
v_res_2999_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_2985_, v_type_2986_, v_val_2987_, v_k_2988_, v_nondep_boxed_2997_, v_kind_boxed_2998_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
return v_res_2999_;
}
}
lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(lean_object* v_k_3000_, uint8_t v_usedLetOnly_3001_, lean_object* v_x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v___x_3009_; 
lean_inc(v___y_3007_);
lean_inc_ref(v___y_3006_);
lean_inc(v___y_3005_);
lean_inc_ref(v___y_3004_);
lean_inc(v___y_3003_);
lean_inc_ref(v_x_3002_);
v___x_3009_ = lean_apply_7(v_k_3000_, v_x_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, lean_box(0));
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_a_3010_);
lean_dec_ref_known(v___x_3009_, 1);
v___x_3011_ = lean_unsigned_to_nat(1u);
v___x_3012_ = lean_mk_empty_array_with_capacity(v___x_3011_);
v___x_3013_ = lean_array_push(v___x_3012_, v_x_3002_);
v___x_3014_ = 0;
v___x_3015_ = 1;
v___x_3016_ = l_Lean_Meta_mkLetFVars(v___x_3013_, v_a_3010_, v_usedLetOnly_3001_, v___x_3014_, v___x_3015_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec_ref(v___x_3013_);
return v___x_3016_;
}
else
{
lean_dec_ref(v_x_3002_);
return v___x_3009_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3000_ = stack[0].m_obj;
uint8_t v_usedLetOnly_3001_ = stack[1].m_num;
lean_object* v_x_3002_ = stack[2].m_obj;
lean_object* v___y_3003_ = stack[3].m_obj;
lean_object* v___y_3004_ = stack[4].m_obj;
lean_object* v___y_3005_ = stack[5].m_obj;
lean_object* v___y_3006_ = stack[6].m_obj;
lean_object* v___y_3007_ = stack[7].m_obj;
lean_object* v_res_3017_;
v_res_3017_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_3000_, v_usedLetOnly_3001_, v_x_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
stack->m_obj
 = v_res_3017_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed(lean_object* v_k_3018_, lean_object* v_usedLetOnly_3019_, lean_object* v_x_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_){
_start:
{
uint8_t v_usedLetOnly_boxed_3027_; lean_object* v_res_3028_; 
v_usedLetOnly_boxed_3027_ = lean_unbox(v_usedLetOnly_3019_);
v_res_3028_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0(v_k_3018_, v_usedLetOnly_boxed_3027_, v_x_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
return v_res_3028_;
}
}
lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(lean_object* v_name_3029_, lean_object* v_type_3030_, lean_object* v_val_3031_, lean_object* v_k_3032_, uint8_t v_nondep_3033_, uint8_t v_kind_3034_, uint8_t v_usedLetOnly_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___f_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_box(v_usedLetOnly_3035_);
v___f_3043_ = lean_alloc_closure((void*)(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3043_, 0, v_k_3032_);
lean_closure_set(v___f_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3029_, v_type_3030_, v_val_3031_, v___f_3043_, v_nondep_3033_, v_kind_3034_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3044_;
}
}
LEAN_EXPORT void l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3029_ = stack[0].m_obj;
lean_object* v_type_3030_ = stack[1].m_obj;
lean_object* v_val_3031_ = stack[2].m_obj;
lean_object* v_k_3032_ = stack[3].m_obj;
uint8_t v_nondep_3033_ = stack[4].m_num;
uint8_t v_kind_3034_ = stack[5].m_num;
uint8_t v_usedLetOnly_3035_ = stack[6].m_num;
lean_object* v___y_3036_ = stack[7].m_obj;
lean_object* v___y_3037_ = stack[8].m_obj;
lean_object* v___y_3038_ = stack[9].m_obj;
lean_object* v___y_3039_ = stack[10].m_obj;
lean_object* v___y_3040_ = stack[11].m_obj;
lean_object* v_res_3045_;
v_res_3045_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_3029_, v_type_3030_, v_val_3031_, v_k_3032_, v_nondep_3033_, v_kind_3034_, v_usedLetOnly_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
stack->m_obj
 = v_res_3045_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4___boxed(lean_object* v_name_3046_, lean_object* v_type_3047_, lean_object* v_val_3048_, lean_object* v_k_3049_, lean_object* v_nondep_3050_, lean_object* v_kind_3051_, lean_object* v_usedLetOnly_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
uint8_t v_nondep_boxed_3059_; uint8_t v_kind_boxed_3060_; uint8_t v_usedLetOnly_boxed_3061_; lean_object* v_res_3062_; 
v_nondep_boxed_3059_ = lean_unbox(v_nondep_3050_);
v_kind_boxed_3060_ = lean_unbox(v_kind_3051_);
v_usedLetOnly_boxed_3061_ = lean_unbox(v_usedLetOnly_3052_);
v_res_3062_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_name_3046_, v_type_3047_, v_val_3048_, v_k_3049_, v_nondep_boxed_3059_, v_kind_boxed_3060_, v_usedLetOnly_boxed_3061_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
return v_res_3062_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(lean_object* v_recArgInfos_3063_, lean_object* v_positions_3064_, lean_object* v_recFnNames_3065_, lean_object* v_containsRecFn_3066_, lean_object* v_below_3067_, size_t v_sz_3068_, size_t v_i_3069_, lean_object* v_bs_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
uint8_t v___x_3077_; 
v___x_3077_ = lean_usize_dec_lt(v_i_3069_, v_sz_3068_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; 
lean_dec_ref(v_below_3067_);
lean_dec_ref(v_containsRecFn_3066_);
lean_dec_ref(v_recFnNames_3065_);
lean_dec_ref(v_positions_3064_);
lean_dec_ref(v_recArgInfos_3063_);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v_bs_3070_);
return v___x_3078_;
}
else
{
lean_object* v_v_3079_; lean_object* v___x_3080_; lean_object* v_bs_x27_3081_; lean_object* v___x_3082_; 
v_v_3079_ = lean_array_uget(v_bs_3070_, v_i_3069_);
v___x_3080_ = lean_unsigned_to_nat(0u);
v_bs_x27_3081_ = lean_array_uset(v_bs_3070_, v_i_3069_, v___x_3080_);
lean_inc_ref(v___y_3074_);
lean_inc_ref(v_below_3067_);
lean_inc_ref(v_containsRecFn_3066_);
lean_inc_ref(v_recFnNames_3065_);
lean_inc_ref(v_positions_3064_);
lean_inc_ref(v_recArgInfos_3063_);
v___x_3082_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3063_, v_positions_3064_, v_recFnNames_3065_, v_containsRecFn_3066_, v_below_3067_, v_v_3079_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc(v_a_3083_);
lean_dec_ref_known(v___x_3082_, 1);
v___x_3084_ = ((size_t)1ULL);
v___x_3085_ = lean_usize_add(v_i_3069_, v___x_3084_);
v___x_3086_ = lean_array_uset(v_bs_x27_3081_, v_i_3069_, v_a_3083_);
v_i_3069_ = v___x_3085_;
v_bs_3070_ = v___x_3086_;
goto _start;
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref(v_bs_x27_3081_);
lean_dec_ref(v_below_3067_);
lean_dec_ref(v_containsRecFn_3066_);
lean_dec_ref(v_recFnNames_3065_);
lean_dec_ref(v_positions_3064_);
lean_dec_ref(v_recArgInfos_3063_);
v_a_3088_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3082_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3082_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_3063_ = stack[0].m_obj;
lean_object* v_positions_3064_ = stack[1].m_obj;
lean_object* v_recFnNames_3065_ = stack[2].m_obj;
lean_object* v_containsRecFn_3066_ = stack[3].m_obj;
lean_object* v_below_3067_ = stack[4].m_obj;
size_t v_sz_3068_ = stack[5].m_num;
size_t v_i_3069_ = stack[6].m_num;
lean_object* v_bs_3070_ = stack[7].m_obj;
lean_object* v___y_3071_ = stack[8].m_obj;
lean_object* v___y_3072_ = stack[9].m_obj;
lean_object* v___y_3073_ = stack[10].m_obj;
lean_object* v___y_3074_ = stack[11].m_obj;
lean_object* v___y_3075_ = stack[12].m_obj;
lean_object* v_res_3096_;
v_res_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3063_, v_positions_3064_, v_recFnNames_3065_, v_containsRecFn_3066_, v_below_3067_, v_sz_3068_, v_i_3069_, v_bs_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
stack->m_obj
 = v_res_3096_;
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__0));
v___x_3099_ = l_Lean_stringToMessageData(v___x_3098_);
return v___x_3099_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__2));
v___x_3102_ = l_Lean_stringToMessageData(v___x_3101_);
return v___x_3102_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(lean_object* v_recArgInfos_3103_, lean_object* v_positions_3104_, lean_object* v_recFnNames_3105_, lean_object* v_containsRecFn_3106_, lean_object* v_below_3107_, lean_object* v_e_3108_, lean_object* v_x_3109_, lean_object* v_x_3110_, lean_object* v_x_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
if (lean_obj_tag(v_x_3109_) == 5)
{
lean_object* v_fn_3118_; lean_object* v_arg_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; 
v_fn_3118_ = lean_ctor_get(v_x_3109_, 0);
lean_inc_ref(v_fn_3118_);
v_arg_3119_ = lean_ctor_get(v_x_3109_, 1);
lean_inc_ref(v_arg_3119_);
lean_dec_ref_known(v_x_3109_, 2);
v___x_3120_ = lean_array_set(v_x_3110_, v_x_3111_, v_arg_3119_);
v___x_3121_ = lean_unsigned_to_nat(1u);
v___x_3122_ = lean_nat_sub(v_x_3111_, v___x_3121_);
lean_dec(v_x_3111_);
v_x_3109_ = v_fn_3118_;
v_x_3110_ = v___x_3120_;
v_x_3111_ = v___x_3122_;
goto _start;
}
else
{
lean_object* v___f_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec(v_x_3111_);
lean_inc_ref(v_x_3109_);
v___f_3124_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3124_, 0, v_x_3109_);
v___x_3125_ = lean_unsigned_to_nat(0u);
v___x_3126_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_3124_, v_recArgInfos_3103_, v___x_3125_);
if (lean_obj_tag(v___x_3126_) == 1)
{
lean_object* v_val_3127_; lean_object* v___x_3128_; lean_object* v___y_3130_; lean_object* v_recArgPos_3156_; lean_object* v_indGroupInst_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
lean_dec_ref(v_x_3109_);
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v___x_3128_ = lean_array_fget_borrowed(v_recArgInfos_3103_, v_val_3127_);
v_recArgPos_3156_ = lean_ctor_get(v___x_3128_, 2);
v_indGroupInst_3157_ = lean_ctor_get(v___x_3128_, 4);
v___x_3158_ = lean_array_get_size(v_x_3110_);
v___x_3159_ = lean_nat_dec_lt(v_recArgPos_3156_, v___x_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
lean_dec(v_val_3127_);
lean_dec_ref(v_x_3110_);
lean_dec_ref(v_below_3107_);
lean_dec_ref(v_containsRecFn_3106_);
lean_dec_ref(v_recFnNames_3105_);
lean_dec_ref(v_positions_3104_);
lean_dec_ref(v_recArgInfos_3103_);
v___x_3160_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__1);
v___x_3161_ = l_Lean_indentExpr(v_e_3108_);
v___x_3162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3162_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
return v___x_3163_;
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = lean_array_fget_borrowed(v_x_3110_, v_recArgPos_3156_);
lean_inc_ref(v___y_3115_);
lean_inc(v___x_3164_);
lean_inc_ref(v_below_3107_);
lean_inc_ref(v_containsRecFn_3106_);
lean_inc_ref(v_recFnNames_3105_);
lean_inc_ref(v_positions_3104_);
lean_inc_ref(v_recArgInfos_3103_);
v___x_3165_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3103_, v_positions_3104_, v_recFnNames_3105_, v_containsRecFn_3106_, v_below_3107_, v___x_3164_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v_params_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v_params_3167_ = lean_ctor_get(v_indGroupInst_3157_, 2);
v___x_3168_ = lean_array_get_size(v_params_3167_);
lean_inc_ref(v_positions_3104_);
lean_inc_ref(v_below_3107_);
v___x_3169_ = l_Lean_Elab_Structural_toBelow(v_below_3107_, v___x_3168_, v_positions_3104_, v_val_3127_, v_a_3166_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_dec_ref(v_e_3108_);
v___y_3130_ = v___x_3169_;
goto v___jp_3129_;
}
else
{
lean_object* v_a_3170_; uint8_t v___y_3172_; uint8_t v___x_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v___x_3177_ = l_Lean_Exception_isInterrupt(v_a_3170_);
if (v___x_3177_ == 0)
{
uint8_t v___x_3178_; 
lean_inc(v_a_3170_);
v___x_3178_ = l_Lean_Exception_isRuntime(v_a_3170_);
v___y_3172_ = v___x_3178_;
goto v___jp_3171_;
}
else
{
v___y_3172_ = v___x_3177_;
goto v___jp_3171_;
}
v___jp_3171_:
{
if (v___y_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
lean_dec_ref_known(v___x_3169_, 1);
v___x_3173_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___closed__3);
v___x_3174_ = l_Lean_indentExpr(v_e_3108_);
v___x_3175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3173_);
lean_ctor_set(v___x_3175_, 1, v___x_3174_);
v___x_3176_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3175_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
v___y_3130_ = v___x_3176_;
goto v___jp_3129_;
}
else
{
lean_dec_ref(v_e_3108_);
v___y_3130_ = v___x_3169_;
goto v___jp_3129_;
}
}
}
}
else
{
lean_dec(v_val_3127_);
lean_dec_ref(v_x_3110_);
lean_dec_ref(v_e_3108_);
lean_dec_ref(v_below_3107_);
lean_dec_ref(v_containsRecFn_3106_);
lean_dec_ref(v_recFnNames_3105_);
lean_dec_ref(v_positions_3104_);
lean_dec_ref(v_recArgInfos_3103_);
return v___x_3165_;
}
}
v___jp_3129_:
{
if (lean_obj_tag(v___y_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v_fixedParamPerm_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v_snd_3135_; size_t v_sz_3136_; size_t v___x_3137_; lean_object* v___x_3138_; 
v_a_3131_ = lean_ctor_get(v___y_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___y_3130_, 1);
v_fixedParamPerm_3132_ = lean_ctor_get(v___x_3128_, 1);
v___x_3133_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(v_fixedParamPerm_3132_, v_x_3110_);
lean_dec_ref(v_x_3110_);
lean_inc(v___x_3128_);
v___x_3134_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v___x_3128_, v___x_3133_);
v_snd_3135_ = lean_ctor_get(v___x_3134_, 1);
lean_inc(v_snd_3135_);
lean_dec_ref(v___x_3134_);
v_sz_3136_ = lean_array_size(v_snd_3135_);
v___x_3137_ = ((size_t)0ULL);
v___x_3138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3103_, v_positions_3104_, v_recFnNames_3105_, v_containsRecFn_3106_, v_below_3107_, v_sz_3136_, v___x_3137_, v_snd_3135_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3147_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3147_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3143_ = l_Lean_mkAppN(v_a_3131_, v_a_3139_);
lean_dec(v_a_3139_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3143_);
v___x_3145_ = v___x_3141_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_a_3131_);
v_a_3148_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3138_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3138_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_dec_ref(v_x_3110_);
lean_dec_ref(v_below_3107_);
lean_dec_ref(v_containsRecFn_3106_);
lean_dec_ref(v_recFnNames_3105_);
lean_dec_ref(v_positions_3104_);
lean_dec_ref(v_recArgInfos_3103_);
return v___y_3130_;
}
}
}
else
{
lean_object* v___x_3179_; 
lean_dec(v___x_3126_);
lean_dec_ref(v_e_3108_);
lean_inc_ref(v___y_3115_);
lean_inc_ref(v_below_3107_);
lean_inc_ref(v_containsRecFn_3106_);
lean_inc_ref(v_recFnNames_3105_);
lean_inc_ref(v_positions_3104_);
lean_inc_ref(v_recArgInfos_3103_);
v___x_3179_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3103_, v_positions_3104_, v_recFnNames_3105_, v_containsRecFn_3106_, v_below_3107_, v_x_3109_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; size_t v_sz_3181_; size_t v___x_3182_; lean_object* v___x_3183_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
v_sz_3181_ = lean_array_size(v_x_3110_);
v___x_3182_ = ((size_t)0ULL);
v___x_3183_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3103_, v_positions_3104_, v_recFnNames_3105_, v_containsRecFn_3106_, v_below_3107_, v_sz_3181_, v___x_3182_, v_x_3110_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3192_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3186_ = v___x_3183_;
v_isShared_3187_ = v_isSharedCheck_3192_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3192_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = l_Lean_mkAppN(v_a_3180_, v_a_3184_);
lean_dec(v_a_3184_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v___x_3188_);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_a_3180_);
v_a_3193_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3183_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3183_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_dec_ref(v_x_3110_);
lean_dec_ref(v_below_3107_);
lean_dec_ref(v_containsRecFn_3106_);
lean_dec_ref(v_recFnNames_3105_);
lean_dec_ref(v_positions_3104_);
lean_dec_ref(v_recArgInfos_3103_);
return v___x_3179_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_3103_ = stack[0].m_obj;
lean_object* v_positions_3104_ = stack[1].m_obj;
lean_object* v_recFnNames_3105_ = stack[2].m_obj;
lean_object* v_containsRecFn_3106_ = stack[3].m_obj;
lean_object* v_below_3107_ = stack[4].m_obj;
lean_object* v_e_3108_ = stack[5].m_obj;
lean_object* v_x_3109_ = stack[6].m_obj;
lean_object* v_x_3110_ = stack[7].m_obj;
lean_object* v_x_3111_ = stack[8].m_obj;
lean_object* v___y_3112_ = stack[9].m_obj;
lean_object* v___y_3113_ = stack[10].m_obj;
lean_object* v___y_3114_ = stack[11].m_obj;
lean_object* v___y_3115_ = stack[12].m_obj;
lean_object* v___y_3116_ = stack[13].m_obj;
lean_object* v_res_3201_;
v_res_3201_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3103_, v_positions_3104_, v_recFnNames_3105_, v_containsRecFn_3106_, v_below_3107_, v_e_3108_, v_x_3109_, v_x_3110_, v_x_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
stack->m_obj
 = v_res_3201_;
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(lean_object* v_body_3202_, lean_object* v_recArgInfos_3203_, lean_object* v_positions_3204_, lean_object* v_recFnNames_3205_, lean_object* v_containsRecFn_3206_, lean_object* v_below_3207_, uint8_t v___x_3208_, uint8_t v_a_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_expr_instantiate1(v_body_3202_, v_x_3210_);
lean_inc_ref(v___y_3214_);
v___x_3218_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3203_, v_positions_3204_, v_recFnNames_3205_, v_containsRecFn_3206_, v_below_3207_, v___x_3217_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; lean_object* v___x_3224_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = lean_unsigned_to_nat(1u);
v___x_3221_ = lean_mk_empty_array_with_capacity(v___x_3220_);
v___x_3222_ = lean_array_push(v___x_3221_, v_x_3210_);
v___x_3223_ = 1;
v___x_3224_ = l_Lean_Meta_mkLambdaFVars(v___x_3222_, v_a_3219_, v___x_3208_, v_a_3209_, v___x_3208_, v_a_3209_, v___x_3223_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec_ref(v___x_3222_);
return v___x_3224_;
}
else
{
lean_dec_ref(v_x_3210_);
return v___x_3218_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_3202_ = stack[0].m_obj;
lean_object* v_recArgInfos_3203_ = stack[1].m_obj;
lean_object* v_positions_3204_ = stack[2].m_obj;
lean_object* v_recFnNames_3205_ = stack[3].m_obj;
lean_object* v_containsRecFn_3206_ = stack[4].m_obj;
lean_object* v_below_3207_ = stack[5].m_obj;
uint8_t v___x_3208_ = stack[6].m_num;
uint8_t v_a_3209_ = stack[7].m_num;
lean_object* v_x_3210_ = stack[8].m_obj;
lean_object* v___y_3211_ = stack[9].m_obj;
lean_object* v___y_3212_ = stack[10].m_obj;
lean_object* v___y_3213_ = stack[11].m_obj;
lean_object* v___y_3214_ = stack[12].m_obj;
lean_object* v___y_3215_ = stack[13].m_obj;
lean_object* v_res_3225_;
v_res_3225_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3202_, v_recArgInfos_3203_, v_positions_3204_, v_recFnNames_3205_, v_containsRecFn_3206_, v_below_3207_, v___x_3208_, v_a_3209_, v_x_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
stack->m_obj
 = v_res_3225_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed(lean_object* v_body_3226_, lean_object* v_recArgInfos_3227_, lean_object* v_positions_3228_, lean_object* v_recFnNames_3229_, lean_object* v_containsRecFn_3230_, lean_object* v_below_3231_, lean_object* v___x_3232_, lean_object* v_a_3233_, lean_object* v_x_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
uint8_t v___x_29606__boxed_3241_; uint8_t v_a_29607__boxed_3242_; lean_object* v_res_3243_; 
v___x_29606__boxed_3241_ = lean_unbox(v___x_3232_);
v_a_29607__boxed_3242_ = lean_unbox(v_a_3233_);
v_res_3243_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0(v_body_3226_, v_recArgInfos_3227_, v_positions_3228_, v_recFnNames_3229_, v_containsRecFn_3230_, v_below_3231_, v___x_29606__boxed_3241_, v_a_29607__boxed_3242_, v_x_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v_body_3226_);
return v_res_3243_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(lean_object* v_body_3244_, lean_object* v_recArgInfos_3245_, lean_object* v_positions_3246_, lean_object* v_recFnNames_3247_, lean_object* v_containsRecFn_3248_, lean_object* v_below_3249_, uint8_t v___x_3250_, uint8_t v_a_3251_, lean_object* v_x_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3259_ = lean_expr_instantiate1(v_body_3244_, v_x_3252_);
lean_inc_ref(v___y_3256_);
v___x_3260_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3245_, v_positions_3246_, v_recFnNames_3247_, v_containsRecFn_3248_, v_below_3249_, v___x_3259_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; lean_object* v___x_3266_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___x_3262_ = lean_unsigned_to_nat(1u);
v___x_3263_ = lean_mk_empty_array_with_capacity(v___x_3262_);
v___x_3264_ = lean_array_push(v___x_3263_, v_x_3252_);
v___x_3265_ = 1;
v___x_3266_ = l_Lean_Meta_mkForallFVars(v___x_3264_, v_a_3261_, v___x_3250_, v_a_3251_, v_a_3251_, v___x_3265_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec_ref(v___x_3264_);
return v___x_3266_;
}
else
{
lean_dec_ref(v_x_3252_);
return v___x_3260_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_3244_ = stack[0].m_obj;
lean_object* v_recArgInfos_3245_ = stack[1].m_obj;
lean_object* v_positions_3246_ = stack[2].m_obj;
lean_object* v_recFnNames_3247_ = stack[3].m_obj;
lean_object* v_containsRecFn_3248_ = stack[4].m_obj;
lean_object* v_below_3249_ = stack[5].m_obj;
uint8_t v___x_3250_ = stack[6].m_num;
uint8_t v_a_3251_ = stack[7].m_num;
lean_object* v_x_3252_ = stack[8].m_obj;
lean_object* v___y_3253_ = stack[9].m_obj;
lean_object* v___y_3254_ = stack[10].m_obj;
lean_object* v___y_3255_ = stack[11].m_obj;
lean_object* v___y_3256_ = stack[12].m_obj;
lean_object* v___y_3257_ = stack[13].m_obj;
lean_object* v_res_3267_;
v_res_3267_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3244_, v_recArgInfos_3245_, v_positions_3246_, v_recFnNames_3247_, v_containsRecFn_3248_, v_below_3249_, v___x_3250_, v_a_3251_, v_x_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
stack->m_obj
 = v_res_3267_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed(lean_object* v_body_3268_, lean_object* v_recArgInfos_3269_, lean_object* v_positions_3270_, lean_object* v_recFnNames_3271_, lean_object* v_containsRecFn_3272_, lean_object* v_below_3273_, lean_object* v___x_3274_, lean_object* v_a_3275_, lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
uint8_t v___x_29624__boxed_3283_; uint8_t v_a_29625__boxed_3284_; lean_object* v_res_3285_; 
v___x_29624__boxed_3283_ = lean_unbox(v___x_3274_);
v_a_29625__boxed_3284_ = lean_unbox(v_a_3275_);
v_res_3285_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1(v_body_3268_, v_recArgInfos_3269_, v_positions_3270_, v_recFnNames_3271_, v_containsRecFn_3272_, v_below_3273_, v___x_29624__boxed_3283_, v_a_29625__boxed_3284_, v_x_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v_body_3268_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed(lean_object* v_body_3286_, lean_object* v_recArgInfos_3287_, lean_object* v_positions_3288_, lean_object* v_recFnNames_3289_, lean_object* v_containsRecFn_3290_, lean_object* v_below_3291_, lean_object* v_x_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3286_, v_recArgInfos_3287_, v_positions_3288_, v_recFnNames_3289_, v_containsRecFn_3290_, v_below_3291_, v_x_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v_x_3292_);
lean_dec_ref(v_body_3286_);
return v_res_3299_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__0));
v___x_3304_ = l_Lean_stringToMessageData(v___x_3303_);
return v___x_3304_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__2));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__4));
v___x_3310_ = l_Lean_stringToMessageData(v___x_3309_);
return v___x_3310_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__6));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(lean_object* v___x_3314_, lean_object* v_b_3315_, lean_object* v_recArgInfos_3316_, lean_object* v_positions_3317_, lean_object* v_recFnNames_3318_, lean_object* v_containsRecFn_3319_, uint8_t v___x_3320_, uint8_t v_a_3321_, lean_object* v___x_3322_, lean_object* v_a_3323_, lean_object* v_e_3324_, lean_object* v___x_3325_, lean_object* v_xs_3326_, lean_object* v_altBody_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v_toCold_3369_; lean_object* v_options_3370_; uint8_t v_hasTrace_3371_; 
v_toCold_3369_ = lean_ctor_get(v___y_3331_, 0);
v_options_3370_ = lean_ctor_get(v_toCold_3369_, 2);
v_hasTrace_3371_ = lean_ctor_get_uint8(v_options_3370_, sizeof(void*)*1);
if (v_hasTrace_3371_ == 0)
{
lean_dec(v___x_3325_);
v___y_3346_ = v___y_3328_;
v___y_3347_ = v___y_3329_;
v___y_3348_ = v___y_3330_;
v___y_3349_ = v___y_3331_;
v___y_3350_ = v___y_3332_;
goto v___jp_3345_;
}
else
{
lean_object* v_inheritedTraceOptions_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; uint8_t v___x_3375_; 
v_inheritedTraceOptions_3372_ = lean_ctor_get(v_toCold_3369_, 11);
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__0___closed__1));
lean_inc(v___x_3325_);
v___x_3374_ = l_Lean_Name_append(v___x_3373_, v___x_3325_);
v___x_3375_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3372_, v_options_3370_, v___x_3374_);
lean_dec(v___x_3374_);
if (v___x_3375_ == 0)
{
lean_dec(v___x_3325_);
v___y_3346_ = v___y_3328_;
v___y_3347_ = v___y_3329_;
v___y_3348_ = v___y_3330_;
v___y_3349_ = v___y_3331_;
v___y_3350_ = v___y_3332_;
goto v___jp_3345_;
}
else
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3376_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__5);
lean_inc(v_b_3315_);
v___x_3377_ = l_Nat_reprFast(v_b_3315_);
v___x_3378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
v___x_3379_ = l_Lean_MessageData_ofFormat(v___x_3378_);
v___x_3380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3376_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__7);
v___x_3382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
lean_inc_ref(v_xs_3326_);
v___x_3383_ = lean_array_to_list(v_xs_3326_);
v___x_3384_ = lean_box(0);
v___x_3385_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__7(v___x_3383_, v___x_3384_);
v___x_3386_ = l_Lean_MessageData_ofList(v___x_3385_);
v___x_3387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3382_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3325_, v___x_3387_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_dec_ref_known(v___x_3388_, 1);
v___y_3346_ = v___y_3328_;
v___y_3347_ = v___y_3329_;
v___y_3348_ = v___y_3330_;
v___y_3349_ = v___y_3331_;
v___y_3350_ = v___y_3332_;
goto v___jp_3345_;
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v_altBody_3327_);
lean_dec_ref(v_xs_3326_);
lean_dec_ref(v_e_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_containsRecFn_3319_);
lean_dec_ref(v_recFnNames_3318_);
lean_dec_ref(v_positions_3317_);
lean_dec_ref(v_recArgInfos_3316_);
lean_dec(v_b_3315_);
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3388_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3388_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
v___jp_3334_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_array_get_borrowed(v___x_3314_, v_xs_3326_, v_b_3315_);
lean_dec(v_b_3315_);
lean_inc_ref(v___y_3338_);
lean_inc(v___x_3340_);
v___x_3341_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3316_, v_positions_3317_, v_recFnNames_3318_, v_containsRecFn_3319_, v___x_3340_, v_altBody_3327_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = 1;
v___x_3344_ = l_Lean_Meta_mkLambdaFVars(v_xs_3326_, v_a_3342_, v___x_3320_, v_a_3321_, v___x_3320_, v_a_3321_, v___x_3343_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec_ref(v_xs_3326_);
return v___x_3344_;
}
else
{
lean_dec_ref(v_xs_3326_);
return v___x_3341_;
}
}
v___jp_3345_:
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = lean_array_get_size(v_xs_3326_);
v___x_3352_ = lean_nat_dec_eq(v___x_3351_, v___x_3322_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref(v_altBody_3327_);
lean_dec_ref(v_xs_3326_);
lean_dec_ref(v_containsRecFn_3319_);
lean_dec_ref(v_recFnNames_3318_);
lean_dec_ref(v_positions_3317_);
lean_dec_ref(v_recArgInfos_3316_);
lean_dec(v_b_3315_);
v___x_3353_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__1);
v___x_3354_ = l_Lean_indentExpr(v_a_3323_);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = lean_obj_once(&l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3, &l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3_once, _init_l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___closed__3);
v___x_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = l_Lean_indentExpr(v_e_3324_);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v___x_3359_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3360_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3360_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
else
{
lean_dec_ref(v_e_3324_);
lean_dec_ref(v_a_3323_);
v___y_3335_ = v___y_3346_;
v___y_3336_ = v___y_3347_;
v___y_3337_ = v___y_3348_;
v___y_3338_ = v___y_3349_;
v___y_3339_ = v___y_3350_;
goto v___jp_3334_;
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3314_ = stack[0].m_obj;
lean_object* v_b_3315_ = stack[1].m_obj;
lean_object* v_recArgInfos_3316_ = stack[2].m_obj;
lean_object* v_positions_3317_ = stack[3].m_obj;
lean_object* v_recFnNames_3318_ = stack[4].m_obj;
lean_object* v_containsRecFn_3319_ = stack[5].m_obj;
uint8_t v___x_3320_ = stack[6].m_num;
uint8_t v_a_3321_ = stack[7].m_num;
lean_object* v___x_3322_ = stack[8].m_obj;
lean_object* v_a_3323_ = stack[9].m_obj;
lean_object* v_e_3324_ = stack[10].m_obj;
lean_object* v___x_3325_ = stack[11].m_obj;
lean_object* v_xs_3326_ = stack[12].m_obj;
lean_object* v_altBody_3327_ = stack[13].m_obj;
lean_object* v___y_3328_ = stack[14].m_obj;
lean_object* v___y_3329_ = stack[15].m_obj;
lean_object* v___y_3330_ = stack[16].m_obj;
lean_object* v___y_3331_ = stack[17].m_obj;
lean_object* v___y_3332_ = stack[18].m_obj;
lean_object* v_res_3397_;
v_res_3397_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3314_, v_b_3315_, v_recArgInfos_3316_, v_positions_3317_, v_recFnNames_3318_, v_containsRecFn_3319_, v___x_3320_, v_a_3321_, v___x_3322_, v_a_3323_, v_e_3324_, v___x_3325_, v_xs_3326_, v_altBody_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
stack->m_obj
 = v_res_3397_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed(lean_object** _args){
lean_object* v___x_3398_ = _args[0];
lean_object* v_b_3399_ = _args[1];
lean_object* v_recArgInfos_3400_ = _args[2];
lean_object* v_positions_3401_ = _args[3];
lean_object* v_recFnNames_3402_ = _args[4];
lean_object* v_containsRecFn_3403_ = _args[5];
lean_object* v___x_3404_ = _args[6];
lean_object* v_a_3405_ = _args[7];
lean_object* v___x_3406_ = _args[8];
lean_object* v_a_3407_ = _args[9];
lean_object* v_e_3408_ = _args[10];
lean_object* v___x_3409_ = _args[11];
lean_object* v_xs_3410_ = _args[12];
lean_object* v_altBody_3411_ = _args[13];
lean_object* v___y_3412_ = _args[14];
lean_object* v___y_3413_ = _args[15];
lean_object* v___y_3414_ = _args[16];
lean_object* v___y_3415_ = _args[17];
lean_object* v___y_3416_ = _args[18];
lean_object* v___y_3417_ = _args[19];
_start:
{
uint8_t v___x_29700__boxed_3418_; uint8_t v_a_29701__boxed_3419_; lean_object* v_res_3420_; 
v___x_29700__boxed_3418_ = lean_unbox(v___x_3404_);
v_a_29701__boxed_3419_ = lean_unbox(v_a_3405_);
v_res_3420_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0(v___x_3398_, v_b_3399_, v_recArgInfos_3400_, v_positions_3401_, v_recFnNames_3402_, v_containsRecFn_3403_, v___x_29700__boxed_3418_, v_a_29701__boxed_3419_, v___x_3406_, v_a_3407_, v_e_3408_, v___x_3409_, v_xs_3410_, v_altBody_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
lean_dec(v___y_3412_);
lean_dec(v___x_3406_);
lean_dec_ref(v___x_3398_);
return v_res_3420_;
}
}
lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(lean_object* v_recArgInfos_3421_, lean_object* v_positions_3422_, lean_object* v_recFnNames_3423_, lean_object* v_containsRecFn_3424_, uint8_t v_a_3425_, lean_object* v_e_3426_, lean_object* v_as_3427_, lean_object* v_bs_3428_, lean_object* v_i_3429_, lean_object* v_cs_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = lean_array_get_size(v_as_3427_);
v___x_3438_ = lean_nat_dec_lt(v_i_3429_, v___x_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
lean_dec(v_i_3429_);
lean_dec_ref(v_e_3426_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_cs_3430_);
return v___x_3439_;
}
else
{
lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3440_ = lean_array_get_size(v_bs_3428_);
v___x_3441_ = lean_nat_dec_lt(v_i_3429_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3442_; 
lean_dec(v_i_3429_);
lean_dec_ref(v_e_3426_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v___x_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3442_, 0, v_cs_3430_);
return v___x_3442_;
}
else
{
lean_object* v___x_3443_; uint8_t v___x_3444_; lean_object* v___x_3445_; lean_object* v_a_3446_; lean_object* v_b_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___f_3452_; lean_object* v___x_3453_; 
v___x_3443_ = l_Lean_instInhabitedExpr;
v___x_3444_ = 0;
v___x_3445_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v_a_3446_ = lean_array_fget_borrowed(v_as_3427_, v_i_3429_);
v_b_3447_ = lean_array_fget_borrowed(v_bs_3428_, v_i_3429_);
v___x_3448_ = lean_unsigned_to_nat(1u);
v___x_3449_ = lean_nat_add(v_b_3447_, v___x_3448_);
v___x_3450_ = lean_box(v___x_3444_);
v___x_3451_ = lean_box(v_a_3425_);
lean_inc_ref(v_e_3426_);
lean_inc_n(v_a_3446_, 2);
lean_inc(v___x_3449_);
lean_inc_ref(v_containsRecFn_3424_);
lean_inc_ref(v_recFnNames_3423_);
lean_inc_ref(v_positions_3422_);
lean_inc_ref(v_recArgInfos_3421_);
lean_inc(v_b_3447_);
v___f_3452_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___lam__0___boxed), 20, 12);
lean_closure_set(v___f_3452_, 0, v___x_3443_);
lean_closure_set(v___f_3452_, 1, v_b_3447_);
lean_closure_set(v___f_3452_, 2, v_recArgInfos_3421_);
lean_closure_set(v___f_3452_, 3, v_positions_3422_);
lean_closure_set(v___f_3452_, 4, v_recFnNames_3423_);
lean_closure_set(v___f_3452_, 5, v_containsRecFn_3424_);
lean_closure_set(v___f_3452_, 6, v___x_3450_);
lean_closure_set(v___f_3452_, 7, v___x_3451_);
lean_closure_set(v___f_3452_, 8, v___x_3449_);
lean_closure_set(v___f_3452_, 9, v_a_3446_);
lean_closure_set(v___f_3452_, 10, v_e_3426_);
lean_closure_set(v___f_3452_, 11, v___x_3445_);
v___x_3453_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__9___redArg(v_a_3446_, v___x_3449_, v___f_3452_, v___x_3444_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = lean_nat_add(v_i_3429_, v___x_3448_);
lean_dec(v_i_3429_);
v___x_3456_ = lean_array_push(v_cs_3430_, v_a_3454_);
v_i_3429_ = v___x_3455_;
v_cs_3430_ = v___x_3456_;
goto _start;
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec_ref(v_cs_3430_);
lean_dec(v_i_3429_);
lean_dec_ref(v_e_3426_);
lean_dec_ref(v_containsRecFn_3424_);
lean_dec_ref(v_recFnNames_3423_);
lean_dec_ref(v_positions_3422_);
lean_dec_ref(v_recArgInfos_3421_);
v_a_3458_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3453_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3453_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_3421_ = stack[0].m_obj;
lean_object* v_positions_3422_ = stack[1].m_obj;
lean_object* v_recFnNames_3423_ = stack[2].m_obj;
lean_object* v_containsRecFn_3424_ = stack[3].m_obj;
uint8_t v_a_3425_ = stack[4].m_num;
lean_object* v_e_3426_ = stack[5].m_obj;
lean_object* v_as_3427_ = stack[6].m_obj;
lean_object* v_bs_3428_ = stack[7].m_obj;
lean_object* v_i_3429_ = stack[8].m_obj;
lean_object* v_cs_3430_ = stack[9].m_obj;
lean_object* v___y_3431_ = stack[10].m_obj;
lean_object* v___y_3432_ = stack[11].m_obj;
lean_object* v___y_3433_ = stack[12].m_obj;
lean_object* v___y_3434_ = stack[13].m_obj;
lean_object* v___y_3435_ = stack[14].m_obj;
lean_object* v_res_3466_;
v_res_3466_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3421_, v_positions_3422_, v_recFnNames_3423_, v_containsRecFn_3424_, v_a_3425_, v_e_3426_, v_as_3427_, v_bs_3428_, v_i_3429_, v_cs_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
stack->m_obj
 = v_res_3466_;
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2(void){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__1));
v___x_3469_ = l_Lean_stringToMessageData(v___x_3468_);
return v___x_3469_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4(void){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__3));
v___x_3472_ = l_Lean_stringToMessageData(v___x_3471_);
return v___x_3472_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6(void){
_start:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__5));
v___x_3475_ = l_Lean_stringToMessageData(v___x_3474_);
return v___x_3475_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(lean_object* v_recArgInfos_3476_, lean_object* v_positions_3477_, lean_object* v_recFnNames_3478_, lean_object* v_containsRecFn_3479_, lean_object* v_below_3480_, lean_object* v_e_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v_e_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___x_3501_; 
lean_inc_ref(v_containsRecFn_3479_);
lean_inc(v_a_3486_);
lean_inc_ref(v_a_3485_);
lean_inc(v_a_3484_);
lean_inc_ref(v_a_3483_);
lean_inc(v_a_3482_);
lean_inc_ref(v_e_3481_);
v___x_3501_ = lean_apply_7(v_containsRecFn_3479_, v_e_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, lean_box(0));
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3716_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3504_ = v___x_3501_;
v_isShared_3505_ = v_isSharedCheck_3716_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3501_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3716_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
uint8_t v___x_3506_; 
v___x_3506_ = lean_unbox(v_a_3502_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3508_; 
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v_e_3481_);
v___x_3508_ = v___x_3504_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_e_3481_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
else
{
uint8_t v___x_3510_; 
lean_del_object(v___x_3504_);
v___x_3510_ = 0;
switch(lean_obj_tag(v_e_3481_))
{
case 6:
{
lean_object* v_binderName_3511_; lean_object* v_binderType_3512_; lean_object* v_body_3513_; uint8_t v_binderInfo_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; 
v_binderName_3511_ = lean_ctor_get(v_e_3481_, 0);
lean_inc(v_binderName_3511_);
v_binderType_3512_ = lean_ctor_get(v_e_3481_, 1);
lean_inc_ref(v_binderType_3512_);
v_body_3513_ = lean_ctor_get(v_e_3481_, 2);
lean_inc_ref(v_body_3513_);
v_binderInfo_3514_ = lean_ctor_get_uint8(v_e_3481_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3481_, 3);
v___x_3515_ = lean_box(v___x_3510_);
lean_inc_ref(v_below_3480_);
lean_inc_ref(v_containsRecFn_3479_);
lean_inc_ref(v_recFnNames_3478_);
lean_inc_ref(v_positions_3477_);
lean_inc_ref(v_recArgInfos_3476_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3516_, 0, v_body_3513_);
lean_closure_set(v___f_3516_, 1, v_recArgInfos_3476_);
lean_closure_set(v___f_3516_, 2, v_positions_3477_);
lean_closure_set(v___f_3516_, 3, v_recFnNames_3478_);
lean_closure_set(v___f_3516_, 4, v_containsRecFn_3479_);
lean_closure_set(v___f_3516_, 5, v_below_3480_);
lean_closure_set(v___f_3516_, 6, v___x_3515_);
lean_closure_set(v___f_3516_, 7, v_a_3502_);
lean_inc_ref(v_a_3485_);
v___x_3517_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_binderType_3512_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc(v_a_3518_);
lean_dec_ref_known(v___x_3517_, 1);
v___x_3519_ = 0;
v___x_3520_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3511_, v_binderInfo_3514_, v_a_3518_, v___f_3516_, v___x_3519_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
lean_dec_ref(v_a_3485_);
return v___x_3520_;
}
else
{
lean_dec_ref(v___f_3516_);
lean_dec(v_binderName_3511_);
lean_dec_ref(v_a_3485_);
return v___x_3517_;
}
}
case 7:
{
lean_object* v_binderName_3521_; lean_object* v_binderType_3522_; lean_object* v_body_3523_; uint8_t v_binderInfo_3524_; lean_object* v___x_3525_; lean_object* v___f_3526_; lean_object* v___x_3527_; 
v_binderName_3521_ = lean_ctor_get(v_e_3481_, 0);
lean_inc(v_binderName_3521_);
v_binderType_3522_ = lean_ctor_get(v_e_3481_, 1);
lean_inc_ref(v_binderType_3522_);
v_body_3523_ = lean_ctor_get(v_e_3481_, 2);
lean_inc_ref(v_body_3523_);
v_binderInfo_3524_ = lean_ctor_get_uint8(v_e_3481_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3481_, 3);
v___x_3525_ = lean_box(v___x_3510_);
lean_inc_ref(v_below_3480_);
lean_inc_ref(v_containsRecFn_3479_);
lean_inc_ref(v_recFnNames_3478_);
lean_inc_ref(v_positions_3477_);
lean_inc_ref(v_recArgInfos_3476_);
v___f_3526_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__1___boxed), 15, 8);
lean_closure_set(v___f_3526_, 0, v_body_3523_);
lean_closure_set(v___f_3526_, 1, v_recArgInfos_3476_);
lean_closure_set(v___f_3526_, 2, v_positions_3477_);
lean_closure_set(v___f_3526_, 3, v_recFnNames_3478_);
lean_closure_set(v___f_3526_, 4, v_containsRecFn_3479_);
lean_closure_set(v___f_3526_, 5, v_below_3480_);
lean_closure_set(v___f_3526_, 6, v___x_3525_);
lean_closure_set(v___f_3526_, 7, v_a_3502_);
lean_inc_ref(v_a_3485_);
v___x_3527_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_binderType_3522_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3527_) == 0)
{
lean_object* v_a_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; 
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc(v_a_3528_);
lean_dec_ref_known(v___x_3527_, 1);
v___x_3529_ = 0;
v___x_3530_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__3___redArg(v_binderName_3521_, v_binderInfo_3524_, v_a_3528_, v___f_3526_, v___x_3529_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
lean_dec_ref(v_a_3485_);
return v___x_3530_;
}
else
{
lean_dec_ref(v___f_3526_);
lean_dec(v_binderName_3521_);
lean_dec_ref(v_a_3485_);
return v___x_3527_;
}
}
case 8:
{
lean_object* v_declName_3531_; lean_object* v_type_3532_; lean_object* v_value_3533_; lean_object* v_body_3534_; uint8_t v_nondep_3535_; lean_object* v___f_3536_; lean_object* v___x_3537_; 
lean_dec(v_a_3502_);
v_declName_3531_ = lean_ctor_get(v_e_3481_, 0);
lean_inc(v_declName_3531_);
v_type_3532_ = lean_ctor_get(v_e_3481_, 1);
lean_inc_ref(v_type_3532_);
v_value_3533_ = lean_ctor_get(v_e_3481_, 2);
lean_inc_ref(v_value_3533_);
v_body_3534_ = lean_ctor_get(v_e_3481_, 3);
lean_inc_ref(v_body_3534_);
v_nondep_3535_ = lean_ctor_get_uint8(v_e_3481_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_3481_, 4);
lean_inc_ref_n(v_below_3480_, 2);
lean_inc_ref_n(v_containsRecFn_3479_, 2);
lean_inc_ref_n(v_recFnNames_3478_, 2);
lean_inc_ref_n(v_positions_3477_, 2);
lean_inc_ref_n(v_recArgInfos_3476_, 2);
v___f_3536_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2___boxed), 13, 6);
lean_closure_set(v___f_3536_, 0, v_body_3534_);
lean_closure_set(v___f_3536_, 1, v_recArgInfos_3476_);
lean_closure_set(v___f_3536_, 2, v_positions_3477_);
lean_closure_set(v___f_3536_, 3, v_recFnNames_3478_);
lean_closure_set(v___f_3536_, 4, v_containsRecFn_3479_);
lean_closure_set(v___f_3536_, 5, v_below_3480_);
lean_inc_ref(v_a_3485_);
v___x_3537_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_type_3532_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; lean_object* v___x_3539_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
lean_inc_ref(v_a_3485_);
v___x_3539_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_value_3533_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; uint8_t v___x_3541_; lean_object* v___x_3542_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___x_3541_ = 0;
v___x_3542_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4(v_declName_3531_, v_a_3538_, v_a_3540_, v___f_3536_, v_nondep_3535_, v___x_3541_, v___x_3510_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
lean_dec_ref(v_a_3485_);
return v___x_3542_;
}
else
{
lean_dec(v_a_3538_);
lean_dec_ref(v___f_3536_);
lean_dec(v_declName_3531_);
lean_dec_ref(v_a_3485_);
return v___x_3539_;
}
}
else
{
lean_dec_ref(v___f_3536_);
lean_dec_ref(v_value_3533_);
lean_dec(v_declName_3531_);
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
return v___x_3537_;
}
}
case 10:
{
lean_object* v_data_3543_; lean_object* v_expr_3544_; lean_object* v___x_3545_; 
lean_dec(v_a_3502_);
v_data_3543_ = lean_ctor_get(v_e_3481_, 0);
lean_inc(v_data_3543_);
v_expr_3544_ = lean_ctor_get(v_e_3481_, 1);
lean_inc_ref(v_expr_3544_);
v___x_3545_ = l_Lean_getRecAppSyntax_x3f(v_e_3481_);
lean_dec_ref_known(v_e_3481_, 2);
if (lean_obj_tag(v___x_3545_) == 1)
{
lean_object* v_val_3546_; lean_object* v_toCold_3547_; lean_object* v_currRecDepth_3548_; lean_object* v_ref_3549_; uint16_t v_optionFlags_3550_; uint8_t v_suppressElabErrors_3551_; uint8_t v_isRecordingDeps_3552_; lean_object* v_ref_3553_; lean_object* v___x_3554_; 
lean_dec(v_data_3543_);
v_val_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc(v_val_3546_);
lean_dec_ref_known(v___x_3545_, 1);
v_toCold_3547_ = lean_ctor_get(v_a_3485_, 0);
lean_inc_ref(v_toCold_3547_);
v_currRecDepth_3548_ = lean_ctor_get(v_a_3485_, 1);
lean_inc(v_currRecDepth_3548_);
v_ref_3549_ = lean_ctor_get(v_a_3485_, 2);
lean_inc(v_ref_3549_);
v_optionFlags_3550_ = lean_ctor_get_uint16(v_a_3485_, sizeof(void*)*3);
v_suppressElabErrors_3551_ = lean_ctor_get_uint8(v_a_3485_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3552_ = lean_ctor_get_uint8(v_a_3485_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_3485_);
v_ref_3553_ = l_Lean_replaceRef(v_val_3546_, v_ref_3549_);
lean_dec(v_ref_3549_);
lean_dec(v_val_3546_);
v___x_3554_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3554_, 0, v_toCold_3547_);
lean_ctor_set(v___x_3554_, 1, v_currRecDepth_3548_);
lean_ctor_set(v___x_3554_, 2, v_ref_3553_);
lean_ctor_set_uint16(v___x_3554_, sizeof(void*)*3, v_optionFlags_3550_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*3 + 2, v_suppressElabErrors_3551_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*3 + 3, v_isRecordingDeps_3552_);
v_e_3481_ = v_expr_3544_;
v_a_3485_ = v___x_3554_;
goto _start;
}
else
{
lean_object* v___x_3556_; 
lean_dec(v___x_3545_);
v___x_3556_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_expr_3544_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3565_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3565_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3561_ = l_Lean_mkMData(v_data_3543_, v_a_3557_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 0, v___x_3561_);
v___x_3563_ = v___x_3559_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
else
{
lean_dec(v_data_3543_);
return v___x_3556_;
}
}
}
case 11:
{
lean_object* v_typeName_3566_; lean_object* v_idx_3567_; lean_object* v_struct_3568_; lean_object* v___x_3569_; 
lean_dec(v_a_3502_);
v_typeName_3566_ = lean_ctor_get(v_e_3481_, 0);
lean_inc(v_typeName_3566_);
v_idx_3567_ = lean_ctor_get(v_e_3481_, 1);
lean_inc(v_idx_3567_);
v_struct_3568_ = lean_ctor_get(v_e_3481_, 2);
lean_inc_ref(v_struct_3568_);
lean_dec_ref_known(v_e_3481_, 3);
v___x_3569_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_struct_3568_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3578_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3578_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3574_ = l_Lean_mkProj(v_typeName_3566_, v_idx_3567_, v_a_3570_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v___x_3574_);
v___x_3576_ = v___x_3572_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
else
{
lean_dec(v_idx_3567_);
lean_dec(v_typeName_3566_);
return v___x_3569_;
}
}
case 5:
{
uint8_t v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = lean_unbox(v_a_3502_);
lean_inc_ref(v_e_3481_);
v___x_3580_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5(v_e_3481_, v___x_3579_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
if (lean_obj_tag(v_a_3581_) == 0)
{
lean_dec(v_a_3502_);
v_e_3489_ = v_e_3481_;
v___y_3490_ = v_a_3482_;
v___y_3491_ = v_a_3483_;
v___y_3492_ = v_a_3484_;
v___y_3493_ = v_a_3485_;
v___y_3494_ = v_a_3486_;
goto v___jp_3488_;
}
else
{
lean_object* v_val_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v_val_3582_ = lean_ctor_get(v_a_3581_, 0);
lean_inc(v_val_3582_);
lean_dec_ref_known(v_a_3581_, 1);
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_array_get_size(v_recArgInfos_3476_);
v___x_3585_ = lean_nat_dec_lt(v___x_3583_, v___x_3584_);
if (v___x_3585_ == 0)
{
lean_dec(v_val_3582_);
lean_dec(v_a_3502_);
v_e_3489_ = v_e_3481_;
v___y_3490_ = v_a_3482_;
v___y_3491_ = v_a_3483_;
v___y_3492_ = v_a_3484_;
v___y_3493_ = v_a_3485_;
v___y_3494_ = v_a_3486_;
goto v___jp_3488_;
}
else
{
if (v___x_3585_ == 0)
{
lean_dec(v_val_3582_);
lean_dec(v_a_3502_);
v_e_3489_ = v_e_3481_;
v___y_3490_ = v_a_3482_;
v___y_3491_ = v_a_3483_;
v___y_3492_ = v_a_3484_;
v___y_3493_ = v_a_3485_;
v___y_3494_ = v_a_3486_;
goto v___jp_3488_;
}
else
{
size_t v___x_3586_; size_t v___x_3587_; uint8_t v___x_3588_; 
v___x_3586_ = ((size_t)0ULL);
v___x_3587_ = lean_usize_of_nat(v___x_3584_);
v___x_3588_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__6(v_e_3481_, v_recArgInfos_3476_, v___x_3586_, v___x_3587_);
if (v___x_3588_ == 0)
{
lean_dec(v_val_3582_);
lean_dec(v_a_3502_);
v_e_3489_ = v_e_3481_;
v___y_3490_ = v_a_3482_;
v___y_3491_ = v_a_3483_;
v___y_3492_ = v_a_3484_;
v___y_3493_ = v_a_3485_;
v___y_3494_ = v_a_3486_;
goto v___jp_3488_;
}
else
{
lean_object* v_toCold_3589_; lean_object* v_inheritedTraceOptions_3590_; lean_object* v___x_3591_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___x_3662_; 
v_toCold_3589_ = lean_ctor_get(v_a_3485_, 0);
v_inheritedTraceOptions_3590_ = lean_ctor_get(v_toCold_3589_, 11);
v___x_3591_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___closed__3));
v___x_3662_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3591_, v_inheritedTraceOptions_3590_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; uint8_t v___x_3664_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v___x_3664_ = lean_unbox(v_a_3663_);
lean_dec(v_a_3663_);
if (v___x_3664_ == 0)
{
v___y_3593_ = v_a_3482_;
v___y_3594_ = v_a_3483_;
v___y_3595_ = v_a_3484_;
v___y_3596_ = v_a_3485_;
v___y_3597_ = v_a_3486_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3665_; 
lean_inc(v_a_3486_);
lean_inc_ref(v_a_3485_);
lean_inc(v_a_3484_);
lean_inc_ref(v_a_3483_);
lean_inc_ref(v_below_3480_);
v___x_3665_ = lean_infer_type(v_below_3480_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
v___x_3667_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__4);
lean_inc_ref(v_below_3480_);
v___x_3668_ = l_Lean_MessageData_ofExpr(v_below_3480_);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3667_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__6);
v___x_3671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3669_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = l_Lean_MessageData_ofExpr(v_a_3666_);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3671_);
lean_ctor_set(v___x_3673_, 1, v___x_3672_);
v___x_3674_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3591_, v___x_3673_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_dec_ref_known(v___x_3674_, 1);
v___y_3593_ = v_a_3482_;
v___y_3594_ = v_a_3483_;
v___y_3595_ = v_a_3484_;
v___y_3596_ = v_a_3485_;
v___y_3597_ = v_a_3486_;
goto v___jp_3592_;
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec(v_val_3582_);
lean_dec_ref_known(v_e_3481_, 2);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_dec(v_val_3582_);
lean_dec_ref_known(v_e_3481_, 2);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
return v___x_3665_;
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_val_3582_);
lean_dec_ref_known(v_e_3481_, 2);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
v_a_3683_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3662_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3662_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
v___jp_3592_:
{
lean_object* v___x_3598_; 
lean_inc_ref(v_below_3480_);
v___x_3598_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_val_3582_, v_below_3480_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
if (lean_obj_tag(v_a_3599_) == 1)
{
lean_object* v_val_3600_; lean_object* v_toMatcherInfo_3601_; lean_object* v_matcherName_3602_; lean_object* v_matcherLevels_3603_; lean_object* v_params_3604_; lean_object* v_motive_3605_; lean_object* v_discrs_3606_; lean_object* v_alts_3607_; lean_object* v_remaining_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; lean_object* v___x_3612_; 
lean_dec_ref(v_below_3480_);
v_val_3600_ = lean_ctor_get(v_a_3599_, 0);
lean_inc(v_val_3600_);
lean_dec_ref_known(v_a_3599_, 1);
v_toMatcherInfo_3601_ = lean_ctor_get(v_val_3600_, 0);
lean_inc_ref(v_toMatcherInfo_3601_);
v_matcherName_3602_ = lean_ctor_get(v_val_3600_, 1);
lean_inc(v_matcherName_3602_);
v_matcherLevels_3603_ = lean_ctor_get(v_val_3600_, 2);
lean_inc_ref(v_matcherLevels_3603_);
v_params_3604_ = lean_ctor_get(v_val_3600_, 3);
lean_inc_ref(v_params_3604_);
v_motive_3605_ = lean_ctor_get(v_val_3600_, 4);
lean_inc_ref(v_motive_3605_);
v_discrs_3606_ = lean_ctor_get(v_val_3600_, 5);
lean_inc_ref(v_discrs_3606_);
v_alts_3607_ = lean_ctor_get(v_val_3600_, 6);
lean_inc_ref(v_alts_3607_);
v_remaining_3608_ = lean_ctor_get(v_val_3600_, 7);
lean_inc_ref(v_remaining_3608_);
v___x_3609_ = l_Lean_Meta_MatcherApp_altNumParams(v_val_3600_);
v___x_3610_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__0));
v___x_3611_ = lean_unbox(v_a_3502_);
lean_dec(v_a_3502_);
v___x_3612_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v___x_3611_, v_e_3481_, v_alts_3607_, v___x_3609_, v___x_3583_, v___x_3610_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec_ref(v___x_3609_);
lean_dec_ref(v_alts_3607_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3622_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3615_ = v___x_3612_;
v_isShared_3616_ = v_isSharedCheck_3622_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3622_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
v___x_3617_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3617_, 0, v_toMatcherInfo_3601_);
lean_ctor_set(v___x_3617_, 1, v_matcherName_3602_);
lean_ctor_set(v___x_3617_, 2, v_matcherLevels_3603_);
lean_ctor_set(v___x_3617_, 3, v_params_3604_);
lean_ctor_set(v___x_3617_, 4, v_motive_3605_);
lean_ctor_set(v___x_3617_, 5, v_discrs_3606_);
lean_ctor_set(v___x_3617_, 6, v_a_3613_);
lean_ctor_set(v___x_3617_, 7, v_remaining_3608_);
v___x_3618_ = l_Lean_Meta_MatcherApp_toExpr(v___x_3617_);
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 0, v___x_3618_);
v___x_3620_ = v___x_3615_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
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
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref(v_remaining_3608_);
lean_dec_ref(v_discrs_3606_);
lean_dec_ref(v_motive_3605_);
lean_dec_ref(v_params_3604_);
lean_dec_ref(v_matcherLevels_3603_);
lean_dec(v_matcherName_3602_);
lean_dec_ref(v_toMatcherInfo_3601_);
v_a_3623_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3612_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3612_);
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
else
{
lean_object* v_toCold_3631_; lean_object* v_inheritedTraceOptions_3632_; lean_object* v___x_3633_; 
lean_dec(v_a_3599_);
lean_dec(v_a_3502_);
v_toCold_3631_ = lean_ctor_get(v___y_3596_, 0);
v_inheritedTraceOptions_3632_ = lean_ctor_get(v_toCold_3631_, 11);
v___x_3633_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__3(v___x_3591_, v_inheritedTraceOptions_3632_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
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
v_e_3489_ = v_e_3481_;
v___y_3490_ = v___y_3593_;
v___y_3491_ = v___y_3594_;
v___y_3492_ = v___y_3595_;
v___y_3493_ = v___y_3596_;
v___y_3494_ = v___y_3597_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___closed__2);
v___x_3637_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v___x_3591_, v___x_3636_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_dec_ref_known(v___x_3637_, 1);
v_e_3489_ = v_e_3481_;
v___y_3490_ = v___y_3593_;
v___y_3491_ = v___y_3594_;
v___y_3492_ = v___y_3595_;
v___y_3493_ = v___y_3596_;
v___y_3494_ = v___y_3597_;
goto v___jp_3488_;
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec_ref(v___y_3596_);
lean_dec_ref_known(v_e_3481_, 2);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v___y_3596_);
lean_dec_ref_known(v_e_3481_, 2);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
v_a_3646_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3633_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3633_);
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
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec_ref(v___y_3596_);
lean_dec_ref_known(v_e_3481_, 2);
lean_dec(v_a_3502_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
v_a_3654_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3598_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3598_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref_known(v_e_3481_, 2);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
v_a_3691_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3580_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3580_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
default: 
{
lean_object* v___x_3699_; 
lean_dec(v_a_3502_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
lean_inc_ref(v_e_3481_);
v___x_3699_ = l_Lean_Elab_ensureNoRecFn(v_recFnNames_3478_, v_e_3481_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
lean_dec_ref(v_a_3485_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3706_ == 0)
{
lean_object* v_unused_3707_; 
v_unused_3707_ = lean_ctor_get(v___x_3699_, 0);
lean_dec(v_unused_3707_);
v___x_3701_ = v___x_3699_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_dec(v___x_3699_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v_e_3481_);
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_e_3481_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v_e_3481_);
v_a_3708_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3699_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3699_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
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
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v_a_3485_);
lean_dec_ref(v_e_3481_);
lean_dec_ref(v_below_3480_);
lean_dec_ref(v_containsRecFn_3479_);
lean_dec_ref(v_recFnNames_3478_);
lean_dec_ref(v_positions_3477_);
lean_dec_ref(v_recArgInfos_3476_);
v_a_3717_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3501_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3501_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
v___jp_3488_:
{
lean_object* v_dummy_3495_; lean_object* v_nargs_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v_dummy_3495_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux___lam__2___closed__0);
v_nargs_3496_ = l_Lean_Expr_getAppNumArgs(v_e_3489_);
lean_inc(v_nargs_3496_);
v___x_3497_ = lean_mk_array(v_nargs_3496_, v_dummy_3495_);
v___x_3498_ = lean_unsigned_to_nat(1u);
v___x_3499_ = lean_nat_sub(v_nargs_3496_, v___x_3498_);
lean_dec(v_nargs_3496_);
lean_inc_ref(v_e_3489_);
v___x_3500_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_e_3489_, v_e_3489_, v___x_3497_, v___x_3499_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec_ref(v___y_3493_);
return v___x_3500_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_3476_ = stack[0].m_obj;
lean_object* v_positions_3477_ = stack[1].m_obj;
lean_object* v_recFnNames_3478_ = stack[2].m_obj;
lean_object* v_containsRecFn_3479_ = stack[3].m_obj;
lean_object* v_below_3480_ = stack[4].m_obj;
lean_object* v_e_3481_ = stack[5].m_obj;
lean_object* v_a_3482_ = stack[6].m_obj;
lean_object* v_a_3483_ = stack[7].m_obj;
lean_object* v_a_3484_ = stack[8].m_obj;
lean_object* v_a_3485_ = stack[9].m_obj;
lean_object* v_a_3486_ = stack[10].m_obj;
lean_object* v_res_3725_;
v_res_3725_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3476_, v_positions_3477_, v_recFnNames_3478_, v_containsRecFn_3479_, v_below_3480_, v_e_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
stack->m_obj
 = v_res_3725_;
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(lean_object* v_body_3726_, lean_object* v_recArgInfos_3727_, lean_object* v_positions_3728_, lean_object* v_recFnNames_3729_, lean_object* v_containsRecFn_3730_, lean_object* v_below_3731_, lean_object* v_x_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_expr_instantiate1(v_body_3726_, v_x_3732_);
lean_inc_ref(v___y_3736_);
v___x_3740_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3727_, v_positions_3728_, v_recFnNames_3729_, v_containsRecFn_3730_, v_below_3731_, v___x_3739_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3740_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_body_3726_ = stack[0].m_obj;
lean_object* v_recArgInfos_3727_ = stack[1].m_obj;
lean_object* v_positions_3728_ = stack[2].m_obj;
lean_object* v_recFnNames_3729_ = stack[3].m_obj;
lean_object* v_containsRecFn_3730_ = stack[4].m_obj;
lean_object* v_below_3731_ = stack[5].m_obj;
lean_object* v_x_3732_ = stack[6].m_obj;
lean_object* v___y_3733_ = stack[7].m_obj;
lean_object* v___y_3734_ = stack[8].m_obj;
lean_object* v___y_3735_ = stack[9].m_obj;
lean_object* v___y_3736_ = stack[10].m_obj;
lean_object* v___y_3737_ = stack[11].m_obj;
lean_object* v_res_3741_;
v_res_3741_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___lam__2(v_body_3726_, v_recArgInfos_3727_, v_positions_3728_, v_recFnNames_3729_, v_containsRecFn_3730_, v_below_3731_, v_x_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
stack->m_obj
 = v_res_3741_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0___boxed(lean_object* v_recArgInfos_3742_, lean_object* v_positions_3743_, lean_object* v_recFnNames_3744_, lean_object* v_containsRecFn_3745_, lean_object* v_below_3746_, lean_object* v_sz_3747_, lean_object* v_i_3748_, lean_object* v_bs_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
size_t v_sz_boxed_3756_; size_t v_i_boxed_3757_; lean_object* v_res_3758_; 
v_sz_boxed_3756_ = lean_unbox_usize(v_sz_3747_);
lean_dec(v_sz_3747_);
v_i_boxed_3757_ = lean_unbox_usize(v_i_3748_);
lean_dec(v_i_3748_);
v_res_3758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__0(v_recArgInfos_3742_, v_positions_3743_, v_recFnNames_3744_, v_containsRecFn_3745_, v_below_3746_, v_sz_boxed_3756_, v_i_boxed_3757_, v_bs_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
return v_res_3758_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10___boxed(lean_object* v_recArgInfos_3759_, lean_object* v_positions_3760_, lean_object* v_recFnNames_3761_, lean_object* v_containsRecFn_3762_, lean_object* v_a_3763_, lean_object* v_e_3764_, lean_object* v_as_3765_, lean_object* v_bs_3766_, lean_object* v_i_3767_, lean_object* v_cs_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v_a_29658__boxed_3775_; lean_object* v_res_3776_; 
v_a_29658__boxed_3775_ = lean_unbox(v_a_3763_);
v_res_3776_ = l_Array_zipWithMAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__10(v_recArgInfos_3759_, v_positions_3760_, v_recFnNames_3761_, v_containsRecFn_3762_, v_a_29658__boxed_3775_, v_e_3764_, v_as_3765_, v_bs_3766_, v_i_3767_, v_cs_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v_bs_3766_);
lean_dec_ref(v_as_3765_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2___boxed(lean_object* v_recArgInfos_3777_, lean_object* v_positions_3778_, lean_object* v_recFnNames_3779_, lean_object* v_containsRecFn_3780_, lean_object* v_below_3781_, lean_object* v_e_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__2(v_recArgInfos_3777_, v_positions_3778_, v_recFnNames_3779_, v_containsRecFn_3780_, v_below_3781_, v_e_3782_, v_x_3783_, v_x_3784_, v_x_3785_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop___boxed(lean_object* v_recArgInfos_3793_, lean_object* v_positions_3794_, lean_object* v_recFnNames_3795_, lean_object* v_containsRecFn_3796_, lean_object* v_below_3797_, lean_object* v_e_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_res_3805_; 
v_res_3805_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_3793_, v_positions_3794_, v_recFnNames_3795_, v_containsRecFn_3796_, v_below_3797_, v_e_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v_a_3803_);
lean_dec(v_a_3803_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
lean_dec(v_a_3799_);
return v_res_3805_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_object* v_00_u03b1_3806_, lean_object* v_msg_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___redArg(v_msg_3807_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3807_ = stack[1].m_obj;
lean_object* v___y_3808_ = stack[2].m_obj;
lean_object* v___y_3809_ = stack[3].m_obj;
lean_object* v___y_3810_ = stack[4].m_obj;
lean_object* v___y_3811_ = stack[5].m_obj;
lean_object* v___y_3812_ = stack[6].m_obj;
lean_object* v_res_3815_;
v_res_3815_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(lean_box(0), v_msg_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
stack->m_obj
 = v_res_3815_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1___boxed(lean_object* v_00_u03b1_3816_, lean_object* v_msg_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__1(v_00_u03b1_3816_, v_msg_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
return v_res_3824_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_object* v_00_u03b1_3825_, lean_object* v_name_3826_, lean_object* v_type_3827_, lean_object* v_val_3828_, lean_object* v_k_3829_, uint8_t v_nondep_3830_, uint8_t v_kind_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___redArg(v_name_3826_, v_type_3827_, v_val_3828_, v_k_3829_, v_nondep_3830_, v_kind_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
return v___x_3838_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3826_ = stack[1].m_obj;
lean_object* v_type_3827_ = stack[2].m_obj;
lean_object* v_val_3828_ = stack[3].m_obj;
lean_object* v_k_3829_ = stack[4].m_obj;
uint8_t v_nondep_3830_ = stack[5].m_num;
uint8_t v_kind_3831_ = stack[6].m_num;
lean_object* v___y_3832_ = stack[7].m_obj;
lean_object* v___y_3833_ = stack[8].m_obj;
lean_object* v___y_3834_ = stack[9].m_obj;
lean_object* v___y_3835_ = stack[10].m_obj;
lean_object* v___y_3836_ = stack[11].m_obj;
lean_object* v_res_3839_;
v_res_3839_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(lean_box(0), v_name_3826_, v_type_3827_, v_val_3828_, v_k_3829_, v_nondep_3830_, v_kind_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
stack->m_obj
 = v_res_3839_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4___boxed(lean_object* v_00_u03b1_3840_, lean_object* v_name_3841_, lean_object* v_type_3842_, lean_object* v_val_3843_, lean_object* v_k_3844_, lean_object* v_nondep_3845_, lean_object* v_kind_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
uint8_t v_nondep_boxed_3853_; uint8_t v_kind_boxed_3854_; lean_object* v_res_3855_; 
v_nondep_boxed_3853_ = lean_unbox(v_nondep_3845_);
v_kind_boxed_3854_ = lean_unbox(v_kind_3846_);
v_res_3855_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__4_spec__4(v_00_u03b1_3840_, v_name_3841_, v_type_3842_, v_val_3843_, v_k_3844_, v_nondep_boxed_3853_, v_kind_boxed_3854_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
return v_res_3855_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(lean_object* v_declName_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___redArg(v_declName_3856_, v___y_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3856_ = stack[0].m_obj;
lean_object* v___y_3857_ = stack[1].m_obj;
lean_object* v___y_3858_ = stack[2].m_obj;
lean_object* v___y_3859_ = stack[3].m_obj;
lean_object* v___y_3860_ = stack[4].m_obj;
lean_object* v___y_3861_ = stack[5].m_obj;
lean_object* v_res_3864_;
v_res_3864_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
stack->m_obj
 = v_res_3864_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8___boxed(lean_object* v_declName_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__8(v_declName_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
return v_res_3872_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(lean_object* v_cls_3873_, lean_object* v_msg_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___redArg(v_cls_3873_, v_msg_3874_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
return v___x_3881_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3873_ = stack[0].m_obj;
lean_object* v_msg_3874_ = stack[1].m_obj;
lean_object* v___y_3875_ = stack[2].m_obj;
lean_object* v___y_3876_ = stack[3].m_obj;
lean_object* v___y_3877_ = stack[4].m_obj;
lean_object* v___y_3878_ = stack[5].m_obj;
lean_object* v___y_3879_ = stack[6].m_obj;
lean_object* v_res_3882_;
v_res_3882_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3873_, v_msg_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
stack->m_obj
 = v_res_3882_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8___boxed(lean_object* v_cls_3883_, lean_object* v_msg_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__8(v_cls_3883_, v_msg_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
return v_res_3891_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_object* v_00_u03b1_3892_, lean_object* v_constName_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___redArg(v_constName_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
return v___x_3900_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3893_ = stack[1].m_obj;
lean_object* v___y_3894_ = stack[2].m_obj;
lean_object* v___y_3895_ = stack[3].m_obj;
lean_object* v___y_3896_ = stack[4].m_obj;
lean_object* v___y_3897_ = stack[5].m_obj;
lean_object* v___y_3898_ = stack[6].m_obj;
lean_object* v_res_3901_;
v_res_3901_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(lean_box(0), v_constName_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
stack->m_obj
 = v_res_3901_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b1_3902_, lean_object* v_constName_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8(v_00_u03b1_3902_, v_constName_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
return v_res_3910_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_object* v_00_u03b1_3911_, lean_object* v_ref_3912_, lean_object* v_constName_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___redArg(v_ref_3912_, v_constName_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
return v___x_3920_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3912_ = stack[1].m_obj;
lean_object* v_constName_3913_ = stack[2].m_obj;
lean_object* v___y_3914_ = stack[3].m_obj;
lean_object* v___y_3915_ = stack[4].m_obj;
lean_object* v___y_3916_ = stack[5].m_obj;
lean_object* v___y_3917_ = stack[6].m_obj;
lean_object* v___y_3918_ = stack[7].m_obj;
lean_object* v_res_3921_;
v_res_3921_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(lean_box(0), v_ref_3912_, v_constName_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_);
stack->m_obj
 = v_res_3921_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15___boxed(lean_object* v_00_u03b1_3922_, lean_object* v_ref_3923_, lean_object* v_constName_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15(v_00_u03b1_3922_, v_ref_3923_, v_constName_3924_, v___y_3925_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec(v_ref_3923_);
return v_res_3931_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_object* v_00_u03b1_3932_, lean_object* v_ref_3933_, lean_object* v_msg_3934_, lean_object* v_declHint_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___redArg(v_ref_3933_, v_msg_3934_, v_declHint_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3933_ = stack[1].m_obj;
lean_object* v_msg_3934_ = stack[2].m_obj;
lean_object* v_declHint_3935_ = stack[3].m_obj;
lean_object* v___y_3936_ = stack[4].m_obj;
lean_object* v___y_3937_ = stack[5].m_obj;
lean_object* v___y_3938_ = stack[6].m_obj;
lean_object* v___y_3939_ = stack[7].m_obj;
lean_object* v___y_3940_ = stack[8].m_obj;
lean_object* v_res_3943_;
v_res_3943_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(lean_box(0), v_ref_3933_, v_msg_3934_, v_declHint_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
stack->m_obj
 = v_res_3943_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17___boxed(lean_object* v_00_u03b1_3944_, lean_object* v_ref_3945_, lean_object* v_msg_3946_, lean_object* v_declHint_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17(v_00_u03b1_3944_, v_ref_3945_, v_msg_3946_, v_declHint_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec(v_ref_3945_);
return v_res_3954_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(lean_object* v_msg_3955_, lean_object* v_declHint_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___redArg(v_msg_3955_, v_declHint_3956_, v___y_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3955_ = stack[0].m_obj;
lean_object* v_declHint_3956_ = stack[1].m_obj;
lean_object* v___y_3957_ = stack[2].m_obj;
lean_object* v___y_3958_ = stack[3].m_obj;
lean_object* v___y_3959_ = stack[4].m_obj;
lean_object* v___y_3960_ = stack[5].m_obj;
lean_object* v___y_3961_ = stack[6].m_obj;
lean_object* v_res_3964_;
v_res_3964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3955_, v_declHint_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
stack->m_obj
 = v_res_3964_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19___boxed(lean_object* v_msg_3965_, lean_object* v_declHint_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__18_spec__19(v_msg_3965_, v_declHint_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
lean_dec(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
return v_res_3973_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_3974_, lean_object* v_ref_3975_, lean_object* v_msg_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___redArg(v_ref_3975_, v_msg_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3975_ = stack[1].m_obj;
lean_object* v_msg_3976_ = stack[2].m_obj;
lean_object* v___y_3977_ = stack[3].m_obj;
lean_object* v___y_3978_ = stack[4].m_obj;
lean_object* v___y_3979_ = stack[5].m_obj;
lean_object* v___y_3980_ = stack[6].m_obj;
lean_object* v___y_3981_ = stack[7].m_obj;
lean_object* v_res_3984_;
v_res_3984_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(lean_box(0), v_ref_3975_, v_msg_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
stack->m_obj
 = v_res_3984_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_3985_, lean_object* v_ref_3986_, lean_object* v_msg_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop_spec__5_spec__6_spec__8_spec__15_spec__17_spec__19(v_00_u03b1_3985_, v_ref_3986_, v_msg_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec(v_ref_3986_);
return v_res_3994_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(lean_object* v_recFnNames_3995_, lean_object* v_e_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v_fst_4005_; lean_object* v_snd_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4003_ = lean_st_ref_take(v___y_3997_);
v___x_4004_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_3995_, v_e_3996_, v___x_4003_);
v_fst_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_fst_4005_);
v_snd_4006_ = lean_ctor_get(v___x_4004_, 1);
lean_inc(v_snd_4006_);
lean_dec_ref(v___x_4004_);
v___x_4007_ = lean_st_ref_put(v___y_3997_, v_snd_4006_);
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v_fst_4005_);
return v___x_4008_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_recFnNames_3995_ = stack[0].m_obj;
lean_object* v_e_3996_ = stack[1].m_obj;
lean_object* v___y_3997_ = stack[2].m_obj;
lean_object* v___y_3998_ = stack[3].m_obj;
lean_object* v___y_3999_ = stack[4].m_obj;
lean_object* v___y_4000_ = stack[5].m_obj;
lean_object* v___y_4001_ = stack[6].m_obj;
lean_object* v_res_4009_;
v_res_4009_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_3995_, v_e_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_);
stack->m_obj
 = v_res_4009_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed(lean_object* v_recFnNames_4010_, lean_object* v_e_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0(v_recFnNames_4010_, v_e_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v_recFnNames_4010_);
return v_res_4018_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(size_t v_sz_4019_, size_t v_i_4020_, lean_object* v_bs_4021_){
_start:
{
uint8_t v___x_4022_; 
v___x_4022_ = lean_usize_dec_lt(v_i_4020_, v_sz_4019_);
if (v___x_4022_ == 0)
{
return v_bs_4021_;
}
else
{
lean_object* v_v_4023_; lean_object* v_fnName_4024_; lean_object* v___x_4025_; lean_object* v_bs_x27_4026_; size_t v___x_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v_v_4023_ = lean_array_uget_borrowed(v_bs_4021_, v_i_4020_);
v_fnName_4024_ = lean_ctor_get(v_v_4023_, 0);
lean_inc(v_fnName_4024_);
v___x_4025_ = lean_unsigned_to_nat(0u);
v_bs_x27_4026_ = lean_array_uset(v_bs_4021_, v_i_4020_, v___x_4025_);
v___x_4027_ = ((size_t)1ULL);
v___x_4028_ = lean_usize_add(v_i_4020_, v___x_4027_);
v___x_4029_ = lean_array_uset(v_bs_x27_4026_, v_i_4020_, v_fnName_4024_);
v_i_4020_ = v___x_4028_;
v_bs_4021_ = v___x_4029_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4019_ = stack[0].m_num;
size_t v_i_4020_ = stack[1].m_num;
lean_object* v_bs_4021_ = stack[2].m_obj;
lean_object* v_res_4031_;
v_res_4031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_4019_, v_i_4020_, v_bs_4021_);
stack->m_obj
 = v_res_4031_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0___boxed(lean_object* v_sz_4032_, lean_object* v_i_4033_, lean_object* v_bs_4034_){
_start:
{
size_t v_sz_boxed_4035_; size_t v_i_boxed_4036_; lean_object* v_res_4037_; 
v_sz_boxed_4035_ = lean_unbox_usize(v_sz_4032_);
lean_dec(v_sz_4032_);
v_i_boxed_4036_ = lean_unbox_usize(v_i_4033_);
lean_dec(v_i_4033_);
v_res_4037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_boxed_4035_, v_i_boxed_4036_, v_bs_4034_);
return v_res_4037_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4038_ = lean_box(0);
v___x_4039_ = lean_unsigned_to_nat(16u);
v___x_4040_ = lean_mk_array(v___x_4039_, v___x_4038_);
return v___x_4040_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4041_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__0);
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v___x_4041_);
return v___x_4043_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(lean_object* v_recArgInfos_4044_, lean_object* v_positions_4045_, lean_object* v_below_4046_, lean_object* v_e_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
size_t v_sz_4053_; size_t v___x_4054_; lean_object* v_recFnNames_4055_; lean_object* v_containsRecFn_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v_sz_4053_ = lean_array_size(v_recArgInfos_4044_);
v___x_4054_ = ((size_t)0ULL);
lean_inc_ref(v_recArgInfos_4044_);
v_recFnNames_4055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_spec__0(v_sz_4053_, v___x_4054_, v_recArgInfos_4044_);
lean_inc_ref(v_recFnNames_4055_);
v_containsRecFn_4056_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___lam__0___boxed), 8, 1);
lean_closure_set(v_containsRecFn_4056_, 0, v_recFnNames_4055_);
v___x_4057_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___closed__1);
v___x_4058_ = lean_st_mk_ref(v___x_4057_);
lean_inc_ref(v_a_4050_);
v___x_4059_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_loop(v_recArgInfos_4044_, v_positions_4045_, v_recFnNames_4055_, v_containsRecFn_4056_, v_below_4046_, v_e_4047_, v___x_4058_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4068_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4068_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4068_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4064_ = lean_st_ref_get(v___x_4058_);
lean_dec(v___x_4058_);
lean_dec(v___x_4064_);
if (v_isShared_4063_ == 0)
{
v___x_4066_ = v___x_4062_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4060_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
else
{
lean_dec(v___x_4058_);
return v___x_4059_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_4044_ = stack[0].m_obj;
lean_object* v_positions_4045_ = stack[1].m_obj;
lean_object* v_below_4046_ = stack[2].m_obj;
lean_object* v_e_4047_ = stack[3].m_obj;
lean_object* v_a_4048_ = stack[4].m_obj;
lean_object* v_a_4049_ = stack[5].m_obj;
lean_object* v_a_4050_ = stack[6].m_obj;
lean_object* v_a_4051_ = stack[7].m_obj;
lean_object* v_res_4069_;
v_res_4069_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4044_, v_positions_4045_, v_below_4046_, v_e_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
stack->m_obj
 = v_res_4069_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps___boxed(lean_object* v_recArgInfos_4070_, lean_object* v_positions_4071_, lean_object* v_below_4072_, lean_object* v_e_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4070_, v_positions_4071_, v_below_4072_, v_e_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec_ref(v_a_4074_);
return v_res_4079_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(lean_object* v_e_4080_, lean_object* v_k_4081_, uint8_t v_cleanupAnnotations_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v___f_4088_; uint8_t v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___f_4088_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4088_, 0, v_k_4081_);
v___x_4089_ = 1;
v___x_4090_ = 0;
v___x_4091_ = lean_box(0);
v___x_4092_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_4080_, v___x_4089_, v___x_4090_, v___x_4089_, v___x_4090_, v___x_4091_, v___f_4088_, v_cleanupAnnotations_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4092_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4092_);
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
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4092_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4092_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4080_ = stack[0].m_obj;
lean_object* v_k_4081_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_4082_ = stack[2].m_num;
lean_object* v___y_4083_ = stack[3].m_obj;
lean_object* v___y_4084_ = stack[4].m_obj;
lean_object* v___y_4085_ = stack[5].m_obj;
lean_object* v___y_4086_ = stack[6].m_obj;
lean_object* v_res_4109_;
v_res_4109_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4080_, v_k_4081_, v_cleanupAnnotations_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
stack->m_obj
 = v_res_4109_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg___boxed(lean_object* v_e_4110_, lean_object* v_k_4111_, lean_object* v_cleanupAnnotations_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4118_; lean_object* v_res_4119_; 
v_cleanupAnnotations_boxed_4118_ = lean_unbox(v_cleanupAnnotations_4112_);
v_res_4119_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4110_, v_k_4111_, v_cleanupAnnotations_boxed_4118_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4119_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_object* v_00_u03b1_4120_, lean_object* v_e_4121_, lean_object* v_k_4122_, uint8_t v_cleanupAnnotations_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v___x_4129_; 
v___x_4129_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_e_4121_, v_k_4122_, v_cleanupAnnotations_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
return v___x_4129_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4121_ = stack[1].m_obj;
lean_object* v_k_4122_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_4123_ = stack[3].m_num;
lean_object* v___y_4124_ = stack[4].m_obj;
lean_object* v___y_4125_ = stack[5].m_obj;
lean_object* v___y_4126_ = stack[6].m_obj;
lean_object* v___y_4127_ = stack[7].m_obj;
lean_object* v_res_4130_;
v_res_4130_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(lean_box(0), v_e_4121_, v_k_4122_, v_cleanupAnnotations_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
stack->m_obj
 = v_res_4130_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___boxed(lean_object* v_00_u03b1_4131_, lean_object* v_e_4132_, lean_object* v_k_4133_, lean_object* v_cleanupAnnotations_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4140_; lean_object* v_res_4141_; 
v_cleanupAnnotations_boxed_4140_ = lean_unbox(v_cleanupAnnotations_4134_);
v_res_4141_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0(v_00_u03b1_4131_, v_e_4132_, v_k_4133_, v_cleanupAnnotations_boxed_4140_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
return v_res_4141_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(lean_object* v_type_4142_, lean_object* v_recArgInfo_4143_, lean_object* v_xs_4144_, lean_object* v___value_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_Meta_instantiateForall(v_type_4142_, v_xs_4144_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; lean_object* v_fst_4154_; lean_object* v_snd_4155_; uint8_t v___x_4156_; uint8_t v___x_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4143_, v_xs_4144_);
v_fst_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_fst_4154_);
v_snd_4155_ = lean_ctor_get(v___x_4153_, 1);
lean_inc(v_snd_4155_);
lean_dec_ref(v___x_4153_);
v___x_4156_ = 0;
v___x_4157_ = 1;
v___x_4158_ = 1;
v___x_4159_ = l_Lean_Meta_mkForallFVars(v_snd_4155_, v_a_4152_, v___x_4156_, v___x_4157_, v___x_4157_, v___x_4158_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v_snd_4155_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = l_Lean_Meta_mkLambdaFVars(v_fst_4154_, v_a_4160_, v___x_4156_, v___x_4157_, v___x_4156_, v___x_4157_, v___x_4158_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v_fst_4154_);
return v___x_4161_;
}
else
{
lean_dec(v_fst_4154_);
return v___x_4159_;
}
}
else
{
lean_dec_ref(v_xs_4144_);
lean_dec_ref(v_recArgInfo_4143_);
return v___x_4151_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnMotive___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4142_ = stack[0].m_obj;
lean_object* v_recArgInfo_4143_ = stack[1].m_obj;
lean_object* v_xs_4144_ = stack[2].m_obj;
lean_object* v___value_4145_ = stack[3].m_obj;
lean_object* v___y_4146_ = stack[4].m_obj;
lean_object* v___y_4147_ = stack[5].m_obj;
lean_object* v___y_4148_ = stack[6].m_obj;
lean_object* v___y_4149_ = stack[7].m_obj;
lean_object* v_res_4162_;
v_res_4162_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4142_, v_recArgInfo_4143_, v_xs_4144_, v___value_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
stack->m_obj
 = v_res_4162_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed(lean_object* v_type_4163_, lean_object* v_recArgInfo_4164_, lean_object* v_xs_4165_, lean_object* v___value_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Elab_Structural_mkBRecOnMotive___lam__0(v_type_4163_, v_recArgInfo_4164_, v_xs_4165_, v___value_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec_ref(v___value_4166_);
return v_res_4172_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object* v_recArgInfo_4173_, lean_object* v_value_4174_, lean_object* v_type_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v___f_4181_; uint8_t v___x_4182_; lean_object* v___x_4183_; 
v___f_4181_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnMotive___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4181_, 0, v_type_4175_);
lean_closure_set(v___f_4181_, 1, v_recArgInfo_4173_);
v___x_4182_ = 0;
v___x_4183_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4174_, v___f_4181_, v___x_4182_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
return v___x_4183_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnMotive_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfo_4173_ = stack[0].m_obj;
lean_object* v_value_4174_ = stack[1].m_obj;
lean_object* v_type_4175_ = stack[2].m_obj;
lean_object* v_a_4176_ = stack[3].m_obj;
lean_object* v_a_4177_ = stack[4].m_obj;
lean_object* v_a_4178_ = stack[5].m_obj;
lean_object* v_a_4179_ = stack[6].m_obj;
lean_object* v_res_4184_;
v_res_4184_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4173_, v_value_4174_, v_type_4175_, v_a_4176_, v_a_4177_, v_a_4178_, v_a_4179_);
stack->m_obj
 = v_res_4184_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnMotive___boxed(lean_object* v_recArgInfo_4185_, lean_object* v_value_4186_, lean_object* v_type_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v_res_4193_; 
v_res_4193_ = l_Lean_Elab_Structural_mkBRecOnMotive(v_recArgInfo_4185_, v_value_4186_, v_type_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
return v_res_4193_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0(lean_object* v_recArgInfos_4194_, lean_object* v_positions_4195_, lean_object* v_value_4196_, lean_object* v_fst_4197_, lean_object* v_snd_4198_, lean_object* v_below_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; 
lean_inc_ref(v_below_4199_);
v___x_4205_ = l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_replaceRecApps(v_recArgInfos_4194_, v_positions_4195_, v_below_4199_, v_value_4196_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; uint8_t v___x_4213_; uint8_t v___x_4214_; lean_object* v___x_4215_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = lean_unsigned_to_nat(1u);
v___x_4208_ = lean_mk_empty_array_with_capacity(v___x_4207_);
v___x_4209_ = lean_array_push(v___x_4208_, v_below_4199_);
v___x_4210_ = l_Array_append___redArg(v_fst_4197_, v___x_4209_);
lean_dec_ref(v___x_4209_);
v___x_4211_ = l_Array_append___redArg(v___x_4210_, v_snd_4198_);
v___x_4212_ = 0;
v___x_4213_ = 1;
v___x_4214_ = 1;
v___x_4215_ = l_Lean_Meta_mkLambdaFVars(v___x_4211_, v_a_4206_, v___x_4212_, v___x_4213_, v___x_4212_, v___x_4213_, v___x_4214_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec_ref(v___x_4211_);
return v___x_4215_;
}
else
{
lean_dec_ref(v_below_4199_);
lean_dec_ref(v_fst_4197_);
return v___x_4205_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnF___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_4194_ = stack[0].m_obj;
lean_object* v_positions_4195_ = stack[1].m_obj;
lean_object* v_value_4196_ = stack[2].m_obj;
lean_object* v_fst_4197_ = stack[3].m_obj;
lean_object* v_snd_4198_ = stack[4].m_obj;
lean_object* v_below_4199_ = stack[5].m_obj;
lean_object* v___y_4200_ = stack[6].m_obj;
lean_object* v___y_4201_ = stack[7].m_obj;
lean_object* v___y_4202_ = stack[8].m_obj;
lean_object* v___y_4203_ = stack[9].m_obj;
lean_object* v_res_4216_;
v_res_4216_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v_recArgInfos_4194_, v_positions_4195_, v_value_4196_, v_fst_4197_, v_snd_4198_, v_below_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
stack->m_obj
 = v_res_4216_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed(lean_object* v_recArgInfos_4217_, lean_object* v_positions_4218_, lean_object* v_value_4219_, lean_object* v_fst_4220_, lean_object* v_snd_4221_, lean_object* v_below_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_Elab_Structural_mkBRecOnF___lam__0(v_recArgInfos_4217_, v_positions_4218_, v_value_4219_, v_fst_4220_, v_snd_4221_, v_below_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec_ref(v_snd_4221_);
return v_res_4228_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__0));
v___x_4231_ = l_Lean_stringToMessageData(v___x_4230_);
return v___x_4231_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1(lean_object* v_recArgInfo_4232_, lean_object* v_recArgInfos_4233_, lean_object* v_positions_4234_, lean_object* v_FType_4235_, lean_object* v_xs_4236_, lean_object* v_value_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; lean_object* v_fst_4244_; lean_object* v_snd_4245_; lean_object* v___x_4247_; uint8_t v_isShared_4248_; uint8_t v_isSharedCheck_4264_; 
v___x_4243_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_4232_, v_xs_4236_);
v_fst_4244_ = lean_ctor_get(v___x_4243_, 0);
v_snd_4245_ = lean_ctor_get(v___x_4243_, 1);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4247_ = v___x_4243_;
v_isShared_4248_ = v_isSharedCheck_4264_;
goto v_resetjp_4246_;
}
else
{
lean_inc(v_snd_4245_);
lean_inc(v_fst_4244_);
lean_dec(v___x_4243_);
v___x_4247_ = lean_box(0);
v_isShared_4248_ = v_isSharedCheck_4264_;
goto v_resetjp_4246_;
}
v_resetjp_4246_:
{
lean_object* v___f_4249_; lean_object* v___x_4250_; 
lean_inc(v_fst_4244_);
v___f_4249_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__0___boxed), 11, 5);
lean_closure_set(v___f_4249_, 0, v_recArgInfos_4233_);
lean_closure_set(v___f_4249_, 1, v_positions_4234_);
lean_closure_set(v___f_4249_, 2, v_value_4237_);
lean_closure_set(v___f_4249_, 3, v_fst_4244_);
lean_closure_set(v___f_4249_, 4, v_snd_4245_);
v___x_4250_ = l_Lean_Meta_instantiateForall(v_FType_4235_, v_fst_4244_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
lean_dec(v_fst_4244_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4252_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc_n(v_a_4251_, 2);
lean_dec_ref_known(v___x_4250_, 1);
v___x_4252_ = l_Lean_Meta_whnfForall(v_a_4251_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v___x_4252_, 1);
if (lean_obj_tag(v_a_4253_) == 7)
{
lean_object* v_binderName_4254_; lean_object* v_binderType_4255_; uint8_t v_binderInfo_4256_; lean_object* v___x_4257_; 
lean_dec(v_a_4251_);
lean_del_object(v___x_4247_);
v_binderName_4254_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_binderName_4254_);
v_binderType_4255_ = lean_ctor_get(v_a_4253_, 1);
lean_inc_ref(v_binderType_4255_);
v_binderInfo_4256_ = lean_ctor_get_uint8(v_a_4253_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_4253_, 3);
v___x_4257_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_4254_, v_binderInfo_4256_, v_binderType_4255_, v___f_4249_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
return v___x_4257_;
}
else
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4261_; 
lean_dec(v_a_4253_);
lean_dec_ref(v___f_4249_);
v___x_4258_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1, &l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnF___lam__1___closed__1);
v___x_4259_ = l_Lean_indentExpr(v_a_4251_);
if (v_isShared_4248_ == 0)
{
lean_ctor_set_tag(v___x_4247_, 7);
lean_ctor_set(v___x_4247_, 1, v___x_4259_);
lean_ctor_set(v___x_4247_, 0, v___x_4258_);
v___x_4261_ = v___x_4247_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4258_);
lean_ctor_set(v_reuseFailAlloc_4263_, 1, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
lean_object* v___x_4262_; 
v___x_4262_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_4261_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
return v___x_4262_;
}
}
}
else
{
lean_dec(v_a_4251_);
lean_dec_ref(v___f_4249_);
lean_del_object(v___x_4247_);
return v___x_4252_;
}
}
else
{
lean_dec_ref(v___f_4249_);
lean_del_object(v___x_4247_);
return v___x_4250_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnF___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfo_4232_ = stack[0].m_obj;
lean_object* v_recArgInfos_4233_ = stack[1].m_obj;
lean_object* v_positions_4234_ = stack[2].m_obj;
lean_object* v_FType_4235_ = stack[3].m_obj;
lean_object* v_xs_4236_ = stack[4].m_obj;
lean_object* v_value_4237_ = stack[5].m_obj;
lean_object* v___y_4238_ = stack[6].m_obj;
lean_object* v___y_4239_ = stack[7].m_obj;
lean_object* v___y_4240_ = stack[8].m_obj;
lean_object* v___y_4241_ = stack[9].m_obj;
lean_object* v_res_4265_;
v_res_4265_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4232_, v_recArgInfos_4233_, v_positions_4234_, v_FType_4235_, v_xs_4236_, v_value_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
stack->m_obj
 = v_res_4265_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed(lean_object* v_recArgInfo_4266_, lean_object* v_recArgInfos_4267_, lean_object* v_positions_4268_, lean_object* v_FType_4269_, lean_object* v_xs_4270_, lean_object* v_value_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
lean_object* v_res_4277_; 
v_res_4277_ = l_Lean_Elab_Structural_mkBRecOnF___lam__1(v_recArgInfo_4266_, v_recArgInfos_4267_, v_positions_4268_, v_FType_4269_, v_xs_4270_, v_value_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
return v_res_4277_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object* v_recArgInfos_4278_, lean_object* v_positions_4279_, lean_object* v_recArgInfo_4280_, lean_object* v_value_4281_, lean_object* v_FType_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v___f_4288_; uint8_t v___x_4289_; lean_object* v___x_4290_; 
v___f_4288_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnF___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4288_, 0, v_recArgInfo_4280_);
lean_closure_set(v___f_4288_, 1, v_recArgInfos_4278_);
lean_closure_set(v___f_4288_, 2, v_positions_4279_);
lean_closure_set(v___f_4288_, 3, v_FType_4282_);
v___x_4289_ = 0;
v___x_4290_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_4281_, v___f_4288_, v___x_4289_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
return v___x_4290_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnF_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_4278_ = stack[0].m_obj;
lean_object* v_positions_4279_ = stack[1].m_obj;
lean_object* v_recArgInfo_4280_ = stack[2].m_obj;
lean_object* v_value_4281_ = stack[3].m_obj;
lean_object* v_FType_4282_ = stack[4].m_obj;
lean_object* v_a_4283_ = stack[5].m_obj;
lean_object* v_a_4284_ = stack[6].m_obj;
lean_object* v_a_4285_ = stack[7].m_obj;
lean_object* v_a_4286_ = stack[8].m_obj;
lean_object* v_res_4291_;
v_res_4291_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4278_, v_positions_4279_, v_recArgInfo_4280_, v_value_4281_, v_FType_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
stack->m_obj
 = v_res_4291_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnF___boxed(lean_object* v_recArgInfos_4292_, lean_object* v_positions_4293_, lean_object* v_recArgInfo_4294_, lean_object* v_value_4295_, lean_object* v_FType_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lean_Elab_Structural_mkBRecOnF(v_recArgInfos_4292_, v_positions_4293_, v_recArgInfo_4294_, v_value_4295_, v_FType_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
return v_res_4302_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0(lean_object* v_toIndGroupInfo_4303_, lean_object* v_params_4304_, uint8_t v_isIndPred_4305_, lean_object* v_brecOnUniv_4306_, lean_object* v_levels_4307_, lean_object* v_idx_4308_){
_start:
{
lean_object* v_n_4309_; lean_object* v___y_4311_; 
v_n_4309_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(v_toIndGroupInfo_4303_, v_idx_4308_);
if (v_isIndPred_4305_ == 0)
{
lean_object* v___x_4314_; 
v___x_4314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4314_, 0, v_brecOnUniv_4306_);
lean_ctor_set(v___x_4314_, 1, v_levels_4307_);
v___y_4311_ = v___x_4314_;
goto v___jp_4310_;
}
else
{
lean_dec(v_brecOnUniv_4306_);
v___y_4311_ = v_levels_4307_;
goto v___jp_4310_;
}
v___jp_4310_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = l_Lean_Expr_const___override(v_n_4309_, v___y_4311_);
v___x_4313_ = l_Lean_mkAppN(v___x_4312_, v_params_4304_);
return v___x_4313_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnConst___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_toIndGroupInfo_4303_ = stack[0].m_obj;
lean_object* v_params_4304_ = stack[1].m_obj;
uint8_t v_isIndPred_4305_ = stack[2].m_num;
lean_object* v_brecOnUniv_4306_ = stack[3].m_obj;
lean_object* v_levels_4307_ = stack[4].m_obj;
lean_object* v_idx_4308_ = stack[5].m_obj;
lean_object* v_res_4315_;
v_res_4315_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4303_, v_params_4304_, v_isIndPred_4305_, v_brecOnUniv_4306_, v_levels_4307_, v_idx_4308_);
stack->m_obj
 = v_res_4315_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed(lean_object* v_toIndGroupInfo_4316_, lean_object* v_params_4317_, lean_object* v_isIndPred_4318_, lean_object* v_brecOnUniv_4319_, lean_object* v_levels_4320_, lean_object* v_idx_4321_){
_start:
{
uint8_t v_isIndPred_boxed_4322_; lean_object* v_res_4323_; 
v_isIndPred_boxed_4322_ = lean_unbox(v_isIndPred_4318_);
v_res_4323_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4316_, v_params_4317_, v_isIndPred_boxed_4322_, v_brecOnUniv_4319_, v_levels_4320_, v_idx_4321_);
lean_dec(v_idx_4321_);
lean_dec_ref(v_params_4317_);
lean_dec_ref(v_toIndGroupInfo_4316_);
return v_res_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1(lean_object* v_brecOnCons_4324_, lean_object* v_a_4325_, lean_object* v_n_4326_){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_apply_1(v_brecOnCons_4324_, v_n_4326_);
v___x_4328_ = l_Lean_mkAppN(v___x_4327_, v_a_4325_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed(lean_object* v_brecOnCons_4329_, lean_object* v_a_4330_, lean_object* v_n_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__1(v_brecOnCons_4329_, v_a_4330_, v_n_4331_);
lean_dec_ref(v_a_4330_);
return v_res_4332_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2(lean_object* v_x_4333_, lean_object* v_type_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v___x_4340_; 
v___x_4340_ = l_Lean_Meta_getLevel(v_type_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
return v___x_4340_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnConst___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4333_ = stack[0].m_obj;
lean_object* v_type_4334_ = stack[1].m_obj;
lean_object* v___y_4335_ = stack[2].m_obj;
lean_object* v___y_4336_ = stack[3].m_obj;
lean_object* v___y_4337_ = stack[4].m_obj;
lean_object* v___y_4338_ = stack[5].m_obj;
lean_object* v_res_4341_;
v_res_4341_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4333_, v_type_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
stack->m_obj
 = v_res_4341_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___lam__2___boxed(lean_object* v_x_4342_, lean_object* v_type_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__2(v_x_4342_, v_type_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec_ref(v_x_4342_);
return v_res_4349_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(lean_object* v_xs_4350_, size_t v_sz_4351_, size_t v_i_4352_, lean_object* v_bs_4353_){
_start:
{
uint8_t v___x_4354_; 
v___x_4354_ = lean_usize_dec_lt(v_i_4352_, v_sz_4351_);
if (v___x_4354_ == 0)
{
return v_bs_4353_;
}
else
{
lean_object* v___x_4355_; lean_object* v_v_4356_; lean_object* v___x_4357_; lean_object* v_bs_x27_4358_; lean_object* v___x_4359_; size_t v___x_4360_; size_t v___x_4361_; lean_object* v___x_4362_; 
v___x_4355_ = l_Lean_instInhabitedExpr;
v_v_4356_ = lean_array_uget(v_bs_4353_, v_i_4352_);
v___x_4357_ = lean_unsigned_to_nat(0u);
v_bs_x27_4358_ = lean_array_uset(v_bs_4353_, v_i_4352_, v___x_4357_);
v___x_4359_ = lean_array_get_borrowed(v___x_4355_, v_xs_4350_, v_v_4356_);
lean_dec(v_v_4356_);
v___x_4360_ = ((size_t)1ULL);
v___x_4361_ = lean_usize_add(v_i_4352_, v___x_4360_);
lean_inc(v___x_4359_);
v___x_4362_ = lean_array_uset(v_bs_x27_4358_, v_i_4352_, v___x_4359_);
v_i_4352_ = v___x_4361_;
v_bs_4353_ = v___x_4362_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4350_ = stack[0].m_obj;
size_t v_sz_4351_ = stack[1].m_num;
size_t v_i_4352_ = stack[2].m_num;
lean_object* v_bs_4353_ = stack[3].m_obj;
lean_object* v_res_4364_;
v_res_4364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4350_, v_sz_4351_, v_i_4352_, v_bs_4353_);
stack->m_obj
 = v_res_4364_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0___boxed(lean_object* v_xs_4365_, lean_object* v_sz_4366_, lean_object* v_i_4367_, lean_object* v_bs_4368_){
_start:
{
size_t v_sz_boxed_4369_; size_t v_i_boxed_4370_; lean_object* v_res_4371_; 
v_sz_boxed_4369_ = lean_unbox_usize(v_sz_4366_);
lean_dec(v_sz_4366_);
v_i_boxed_4370_ = lean_unbox_usize(v_i_4367_);
lean_dec(v_i_4367_);
v_res_4371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4365_, v_sz_boxed_4369_, v_i_boxed_4370_, v_bs_4368_);
lean_dec_ref(v_xs_4365_);
return v_res_4371_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(lean_object* v_xs_4372_, lean_object* v_f_4373_, lean_object* v_as_4374_, lean_object* v_bs_4375_, lean_object* v_i_4376_, lean_object* v_cs_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; uint8_t v___x_4384_; 
v___x_4383_ = lean_array_get_size(v_as_4374_);
v___x_4384_ = lean_nat_dec_lt(v_i_4376_, v___x_4383_);
if (v___x_4384_ == 0)
{
lean_object* v___x_4385_; 
lean_dec(v_i_4376_);
lean_dec_ref(v_f_4373_);
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v_cs_4377_);
return v___x_4385_;
}
else
{
lean_object* v___x_4386_; uint8_t v___x_4387_; 
v___x_4386_ = lean_array_get_size(v_bs_4375_);
v___x_4387_ = lean_nat_dec_lt(v_i_4376_, v___x_4386_);
if (v___x_4387_ == 0)
{
lean_object* v___x_4388_; 
lean_dec(v_i_4376_);
lean_dec_ref(v_f_4373_);
v___x_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4388_, 0, v_cs_4377_);
return v___x_4388_;
}
else
{
lean_object* v_a_4389_; lean_object* v_b_4390_; size_t v_sz_4391_; size_t v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v_a_4389_ = lean_array_fget_borrowed(v_as_4374_, v_i_4376_);
v_b_4390_ = lean_array_fget_borrowed(v_bs_4375_, v_i_4376_);
v_sz_4391_ = lean_array_size(v_b_4390_);
v___x_4392_ = ((size_t)0ULL);
lean_inc(v_b_4390_);
v___x_4393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__0(v_xs_4372_, v_sz_4391_, v___x_4392_, v_b_4390_);
lean_inc_ref(v_f_4373_);
lean_inc(v___y_4381_);
lean_inc_ref(v___y_4380_);
lean_inc(v___y_4379_);
lean_inc_ref(v___y_4378_);
lean_inc(v_a_4389_);
v___x_4394_ = lean_apply_7(v_f_4373_, v_a_4389_, v___x_4393_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, lean_box(0));
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v___x_4396_ = lean_unsigned_to_nat(1u);
v___x_4397_ = lean_nat_add(v_i_4376_, v___x_4396_);
lean_dec(v_i_4376_);
v___x_4398_ = lean_array_push(v_cs_4377_, v_a_4395_);
v_i_4376_ = v___x_4397_;
v_cs_4377_ = v___x_4398_;
goto _start;
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec_ref(v_cs_4377_);
lean_dec(v_i_4376_);
lean_dec_ref(v_f_4373_);
v_a_4400_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4394_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4394_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4372_ = stack[0].m_obj;
lean_object* v_f_4373_ = stack[1].m_obj;
lean_object* v_as_4374_ = stack[2].m_obj;
lean_object* v_bs_4375_ = stack[3].m_obj;
lean_object* v_i_4376_ = stack[4].m_obj;
lean_object* v_cs_4377_ = stack[5].m_obj;
lean_object* v___y_4378_ = stack[6].m_obj;
lean_object* v___y_4379_ = stack[7].m_obj;
lean_object* v___y_4380_ = stack[8].m_obj;
lean_object* v___y_4381_ = stack[9].m_obj;
lean_object* v_res_4408_;
v_res_4408_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4372_, v_f_4373_, v_as_4374_, v_bs_4375_, v_i_4376_, v_cs_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
stack->m_obj
 = v_res_4408_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg___boxed(lean_object* v_xs_4409_, lean_object* v_f_4410_, lean_object* v_as_4411_, lean_object* v_bs_4412_, lean_object* v_i_4413_, lean_object* v_cs_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4409_, v_f_4410_, v_as_4411_, v_bs_4412_, v_i_4413_, v_cs_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec_ref(v_bs_4412_);
lean_dec_ref(v_as_4411_);
lean_dec_ref(v_xs_4409_);
return v_res_4420_;
}
}
static lean_object* _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Array_instInhabited___redArg();
return v___x_4421_;
}
}
lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(lean_object* v_msg_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4428_; lean_object* v_toApplicative_4429_; lean_object* v_toFunctor_4430_; lean_object* v_toSeq_4431_; lean_object* v_toSeqLeft_4432_; lean_object* v_toSeqRight_4433_; lean_object* v___f_4434_; lean_object* v___f_4435_; lean_object* v___f_4436_; lean_object* v___f_4437_; lean_object* v___x_4438_; lean_object* v___f_4439_; lean_object* v___f_4440_; lean_object* v___f_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v_toApplicative_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4476_; 
v___x_4428_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__1);
v_toApplicative_4429_ = lean_ctor_get(v___x_4428_, 0);
v_toFunctor_4430_ = lean_ctor_get(v_toApplicative_4429_, 0);
v_toSeq_4431_ = lean_ctor_get(v_toApplicative_4429_, 2);
v_toSeqLeft_4432_ = lean_ctor_get(v_toApplicative_4429_, 3);
v_toSeqRight_4433_ = lean_ctor_get(v_toApplicative_4429_, 4);
v___f_4434_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__2));
v___f_4435_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_4430_, 2);
v___f_4436_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4436_, 0, v_toFunctor_4430_);
v___f_4437_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4437_, 0, v_toFunctor_4430_);
v___x_4438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___f_4436_);
lean_ctor_set(v___x_4438_, 1, v___f_4437_);
lean_inc(v_toSeqRight_4433_);
v___f_4439_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4439_, 0, v_toSeqRight_4433_);
lean_inc(v_toSeqLeft_4432_);
v___f_4440_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4440_, 0, v_toSeqLeft_4432_);
lean_inc(v_toSeq_4431_);
v___f_4441_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4441_, 0, v_toSeq_4431_);
v___x_4442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4438_);
lean_ctor_set(v___x_4442_, 1, v___f_4434_);
lean_ctor_set(v___x_4442_, 2, v___f_4441_);
lean_ctor_set(v___x_4442_, 3, v___f_4440_);
lean_ctor_set(v___x_4442_, 4, v___f_4439_);
v___x_4443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4443_, 0, v___x_4442_);
lean_ctor_set(v___x_4443_, 1, v___f_4435_);
v___x_4444_ = l_StateRefT_x27_instMonad___redArg(v___x_4443_);
v_toApplicative_4445_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4476_ == 0)
{
lean_object* v_unused_4477_; 
v_unused_4477_ = lean_ctor_get(v___x_4444_, 1);
lean_dec(v_unused_4477_);
v___x_4447_ = v___x_4444_;
v_isShared_4448_ = v_isSharedCheck_4476_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_toApplicative_4445_);
lean_dec(v___x_4444_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4476_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v_toFunctor_4449_; lean_object* v_toSeq_4450_; lean_object* v_toSeqLeft_4451_; lean_object* v_toSeqRight_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4474_; 
v_toFunctor_4449_ = lean_ctor_get(v_toApplicative_4445_, 0);
v_toSeq_4450_ = lean_ctor_get(v_toApplicative_4445_, 2);
v_toSeqLeft_4451_ = lean_ctor_get(v_toApplicative_4445_, 3);
v_toSeqRight_4452_ = lean_ctor_get(v_toApplicative_4445_, 4);
v_isSharedCheck_4474_ = !lean_is_exclusive(v_toApplicative_4445_);
if (v_isSharedCheck_4474_ == 0)
{
lean_object* v_unused_4475_; 
v_unused_4475_ = lean_ctor_get(v_toApplicative_4445_, 1);
lean_dec(v_unused_4475_);
v___x_4454_ = v_toApplicative_4445_;
v_isShared_4455_ = v_isSharedCheck_4474_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_toSeqRight_4452_);
lean_inc(v_toSeqLeft_4451_);
lean_inc(v_toSeq_4450_);
lean_inc(v_toFunctor_4449_);
lean_dec(v_toApplicative_4445_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4474_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___f_4456_; lean_object* v___f_4457_; lean_object* v___f_4458_; lean_object* v___f_4459_; lean_object* v___x_4460_; lean_object* v___f_4461_; lean_object* v___f_4462_; lean_object* v___f_4463_; lean_object* v___x_4465_; 
v___f_4456_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__4));
v___f_4457_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___closed__5));
lean_inc_ref(v_toFunctor_4449_);
v___f_4458_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4458_, 0, v_toFunctor_4449_);
v___f_4459_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4459_, 0, v_toFunctor_4449_);
v___x_4460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___f_4458_);
lean_ctor_set(v___x_4460_, 1, v___f_4459_);
v___f_4461_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4461_, 0, v_toSeqRight_4452_);
v___f_4462_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4462_, 0, v_toSeqLeft_4451_);
v___f_4463_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4463_, 0, v_toSeq_4450_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 4, v___f_4461_);
lean_ctor_set(v___x_4454_, 3, v___f_4462_);
lean_ctor_set(v___x_4454_, 2, v___f_4463_);
lean_ctor_set(v___x_4454_, 1, v___f_4456_);
lean_ctor_set(v___x_4454_, 0, v___x_4460_);
v___x_4465_ = v___x_4454_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v___x_4460_);
lean_ctor_set(v_reuseFailAlloc_4473_, 1, v___f_4456_);
lean_ctor_set(v_reuseFailAlloc_4473_, 2, v___f_4463_);
lean_ctor_set(v_reuseFailAlloc_4473_, 3, v___f_4462_);
lean_ctor_set(v_reuseFailAlloc_4473_, 4, v___f_4461_);
v___x_4465_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
lean_object* v___x_4467_; 
if (v_isShared_4448_ == 0)
{
lean_ctor_set(v___x_4447_, 1, v___f_4457_);
lean_ctor_set(v___x_4447_, 0, v___x_4465_);
v___x_4467_ = v___x_4447_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v___x_4465_);
lean_ctor_set(v_reuseFailAlloc_4472_, 1, v___f_4457_);
v___x_4467_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_855__overap_4470_; lean_object* v___x_4471_; 
v___x_4468_ = lean_obj_once(&l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0, &l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0_once, _init_l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___closed__0);
v___x_4469_ = l_instInhabitedOfMonad___redArg(v___x_4467_, v___x_4468_);
v___x_855__overap_4470_ = lean_panic_fn_borrowed(v___x_4469_, v_msg_4422_);
lean_dec(v___x_4469_);
lean_inc(v___y_4426_);
lean_inc_ref(v___y_4425_);
lean_inc(v___y_4424_);
lean_inc_ref(v___y_4423_);
v___x_4471_ = lean_apply_5(v___x_855__overap_4470_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, lean_box(0));
return v___x_4471_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4422_ = stack[0].m_obj;
lean_object* v___y_4423_ = stack[1].m_obj;
lean_object* v___y_4424_ = stack[2].m_obj;
lean_object* v___y_4425_ = stack[3].m_obj;
lean_object* v___y_4426_ = stack[4].m_obj;
lean_object* v_res_4478_;
v_res_4478_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
stack->m_obj
 = v_res_4478_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg___boxed(lean_object* v_msg_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
return v_res_4485_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4489_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__2));
v___x_4490_ = lean_unsigned_to_nat(2u);
v___x_4491_ = lean_unsigned_to_nat(73u);
v___x_4492_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4493_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4494_ = l_mkPanicMessageWithDecl(v___x_4493_, v___x_4492_, v___x_4491_, v___x_4490_, v___x_4489_);
return v___x_4494_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4496_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__4));
v___x_4497_ = lean_unsigned_to_nat(2u);
v___x_4498_ = lean_unsigned_to_nat(74u);
v___x_4499_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__1));
v___x_4500_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__0));
v___x_4501_ = l_mkPanicMessageWithDecl(v___x_4500_, v___x_4499_, v___x_4498_, v___x_4497_, v___x_4496_);
return v___x_4501_;
}
}
lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(lean_object* v_f_4504_, lean_object* v_positions_4505_, lean_object* v_ys_4506_, lean_object* v_xs_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; uint8_t v___x_4515_; 
v___x_4513_ = lean_array_get_size(v_positions_4505_);
v___x_4514_ = lean_array_get_size(v_ys_4506_);
v___x_4515_ = lean_nat_dec_eq(v___x_4513_, v___x_4514_);
if (v___x_4515_ == 0)
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
lean_dec_ref(v_f_4504_);
v___x_4516_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__3);
v___x_4517_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4516_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
return v___x_4517_;
}
else
{
lean_object* v___x_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4518_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4505_);
v___x_4519_ = lean_array_get_size(v_xs_4507_);
v___x_4520_ = lean_nat_dec_eq(v___x_4518_, v___x_4519_);
lean_dec(v___x_4518_);
if (v___x_4520_ == 0)
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
lean_dec_ref(v_f_4504_);
v___x_4521_ = lean_obj_once(&l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5, &l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5_once, _init_l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__5);
v___x_4522_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v___x_4521_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
return v___x_4522_;
}
else
{
lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4523_ = lean_unsigned_to_nat(0u);
v___x_4524_ = ((lean_object*)(l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___closed__6));
v___x_4525_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4507_, v_f_4504_, v_ys_4506_, v_positions_4505_, v___x_4523_, v___x_4524_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
return v___x_4525_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4504_ = stack[0].m_obj;
lean_object* v_positions_4505_ = stack[1].m_obj;
lean_object* v_ys_4506_ = stack[2].m_obj;
lean_object* v_xs_4507_ = stack[3].m_obj;
lean_object* v___y_4508_ = stack[4].m_obj;
lean_object* v___y_4509_ = stack[5].m_obj;
lean_object* v___y_4510_ = stack[6].m_obj;
lean_object* v___y_4511_ = stack[7].m_obj;
lean_object* v_res_4526_;
v_res_4526_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4504_, v_positions_4505_, v_ys_4506_, v_xs_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
stack->m_obj
 = v_res_4526_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg___boxed(lean_object* v_f_4527_, lean_object* v_positions_4528_, lean_object* v_ys_4529_, lean_object* v_xs_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4527_, v_positions_4528_, v_ys_4529_, v_xs_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v_xs_4530_);
lean_dec_ref(v_ys_4529_);
lean_dec_ref(v_positions_4528_);
return v_res_4536_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = lean_unsigned_to_nat(0u);
v___x_4539_ = l_Lean_Level_ofNat(v___x_4538_);
return v___x_4539_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object* v_recArgInfos_4540_, lean_object* v_positions_4541_, lean_object* v_motives_4542_, uint8_t v_isIndPred_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_){
_start:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v_indGroupInst_4552_; lean_object* v_brecOnUniv_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; 
v___x_4549_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4550_ = lean_unsigned_to_nat(0u);
v___x_4551_ = lean_array_get_borrowed(v___x_4549_, v_recArgInfos_4540_, v___x_4550_);
v_indGroupInst_4552_ = lean_ctor_get(v___x_4551_, 4);
if (v_isIndPred_4543_ == 0)
{
lean_object* v___f_4595_; lean_object* v___x_4596_; lean_object* v_motive_4597_; lean_object* v___x_4598_; 
v___f_4595_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnConst___closed__0));
v___x_4596_ = l_Lean_instInhabitedExpr;
v_motive_4597_ = lean_array_get_borrowed(v___x_4596_, v_motives_4542_, v___x_4550_);
lean_inc(v_motive_4597_);
v___x_4598_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_motive_4597_, v___f_4595_, v_isIndPred_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
v_brecOnUniv_4554_ = v_a_4599_;
v___y_4555_ = v_a_4544_;
v___y_4556_ = v_a_4545_;
v___y_4557_ = v_a_4546_;
v___y_4558_ = v_a_4547_;
goto v___jp_4553_;
}
else
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4607_; 
v_a_4600_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4602_ = v___x_4598_;
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4598_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4607_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4605_; 
if (v_isShared_4603_ == 0)
{
v___x_4605_ = v___x_4602_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v_a_4600_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
}
}
else
{
lean_object* v___x_4608_; 
v___x_4608_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v_brecOnUniv_4554_ = v___x_4608_;
v___y_4555_ = v_a_4544_;
v___y_4556_ = v_a_4545_;
v___y_4557_ = v_a_4546_;
v___y_4558_ = v_a_4547_;
goto v___jp_4553_;
}
v___jp_4553_:
{
lean_object* v_toIndGroupInfo_4559_; lean_object* v_levels_4560_; lean_object* v_params_4561_; lean_object* v___x_4562_; lean_object* v_brecOnCons_4563_; lean_object* v_brecOnAux_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v_toIndGroupInfo_4559_ = lean_ctor_get(v_indGroupInst_4552_, 0);
v_levels_4560_ = lean_ctor_get(v_indGroupInst_4552_, 1);
v_params_4561_ = lean_ctor_get(v_indGroupInst_4552_, 2);
v___x_4562_ = lean_box(v_isIndPred_4543_);
lean_inc_n(v_levels_4560_, 2);
lean_inc(v_brecOnUniv_4554_);
lean_inc_ref(v_params_4561_);
lean_inc_ref(v_toIndGroupInfo_4559_);
v_brecOnCons_4563_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__0___boxed), 6, 5);
lean_closure_set(v_brecOnCons_4563_, 0, v_toIndGroupInfo_4559_);
lean_closure_set(v_brecOnCons_4563_, 1, v_params_4561_);
lean_closure_set(v_brecOnCons_4563_, 2, v___x_4562_);
lean_closure_set(v_brecOnCons_4563_, 3, v_brecOnUniv_4554_);
lean_closure_set(v_brecOnCons_4563_, 4, v_levels_4560_);
v_brecOnAux_4564_ = l_Lean_Elab_Structural_mkBRecOnConst___lam__0(v_toIndGroupInfo_4559_, v_params_4561_, v_isIndPred_4543_, v_brecOnUniv_4554_, v_levels_4560_, v___x_4550_);
v___x_4565_ = l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_4559_);
v___x_4566_ = l_Lean_Meta_inferArgumentTypesN(v___x_4565_, v_brecOnAux_4564_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref_known(v___x_4566_, 1);
v___x_4568_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_withBelowDict___redArg___lam__5___closed__0));
v___x_4569_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v___x_4568_, v_positions_4541_, v_a_4567_, v_motives_4542_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v_a_4567_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4578_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4572_ = v___x_4569_;
v_isShared_4573_ = v_isSharedCheck_4578_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4569_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4578_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___f_4574_; lean_object* v___x_4576_; 
v___f_4574_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnConst___lam__1___boxed), 3, 2);
lean_closure_set(v___f_4574_, 0, v_brecOnCons_4563_);
lean_closure_set(v___f_4574_, 1, v_a_4570_);
if (v_isShared_4573_ == 0)
{
lean_ctor_set(v___x_4572_, 0, v___f_4574_);
v___x_4576_ = v___x_4572_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___f_4574_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec_ref(v_brecOnCons_4563_);
v_a_4579_ = lean_ctor_get(v___x_4569_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4569_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4569_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_dec_ref(v_brecOnCons_4563_);
v_a_4587_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4566_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4566_);
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
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnConst_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_4540_ = stack[0].m_obj;
lean_object* v_positions_4541_ = stack[1].m_obj;
lean_object* v_motives_4542_ = stack[2].m_obj;
uint8_t v_isIndPred_4543_ = stack[3].m_num;
lean_object* v_a_4544_ = stack[4].m_obj;
lean_object* v_a_4545_ = stack[5].m_obj;
lean_object* v_a_4546_ = stack[6].m_obj;
lean_object* v_a_4547_ = stack[7].m_obj;
lean_object* v_res_4609_;
v_res_4609_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4540_, v_positions_4541_, v_motives_4542_, v_isIndPred_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_);
stack->m_obj
 = v_res_4609_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnConst___boxed(lean_object* v_recArgInfos_4610_, lean_object* v_positions_4611_, lean_object* v_motives_4612_, lean_object* v_isIndPred_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
uint8_t v_isIndPred_boxed_4619_; lean_object* v_res_4620_; 
v_isIndPred_boxed_4619_ = lean_unbox(v_isIndPred_4613_);
v_res_4620_ = l_Lean_Elab_Structural_mkBRecOnConst(v_recArgInfos_4610_, v_positions_4611_, v_motives_4612_, v_isIndPred_boxed_4619_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_motives_4612_);
lean_dec_ref(v_positions_4611_);
lean_dec_ref(v_recArgInfos_4610_);
return v_res_4620_;
}
}
lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_object* v_00_u03b3_4621_, lean_object* v_msg_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
lean_object* v___x_4628_; 
v___x_4628_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___redArg(v_msg_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
return v___x_4628_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_4622_ = stack[1].m_obj;
lean_object* v___y_4623_ = stack[2].m_obj;
lean_object* v___y_4624_ = stack[3].m_obj;
lean_object* v___y_4625_ = stack[4].m_obj;
lean_object* v___y_4626_ = stack[5].m_obj;
lean_object* v_res_4629_;
v_res_4629_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(lean_box(0), v_msg_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
stack->m_obj
 = v_res_4629_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1___boxed(lean_object* v_00_u03b3_4630_, lean_object* v_msg_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_){
_start:
{
lean_object* v_res_4637_; 
v_res_4637_ = l_panic___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__1(v_00_u03b3_4630_, v_msg_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
return v_res_4637_;
}
}
lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_object* v_00_u03b3_4638_, lean_object* v_00_u03b1_4639_, lean_object* v_f_4640_, lean_object* v_positions_4641_, lean_object* v_ys_4642_, lean_object* v_xs_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v___x_4649_; 
v___x_4649_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___redArg(v_f_4640_, v_positions_4641_, v_ys_4642_, v_xs_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
return v___x_4649_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_4640_ = stack[2].m_obj;
lean_object* v_positions_4641_ = stack[3].m_obj;
lean_object* v_ys_4642_ = stack[4].m_obj;
lean_object* v_xs_4643_ = stack[5].m_obj;
lean_object* v___y_4644_ = stack[6].m_obj;
lean_object* v___y_4645_ = stack[7].m_obj;
lean_object* v___y_4646_ = stack[8].m_obj;
lean_object* v___y_4647_ = stack[9].m_obj;
lean_object* v_res_4650_;
v_res_4650_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(lean_box(0), lean_box(0), v_f_4640_, v_positions_4641_, v_ys_4642_, v_xs_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
stack->m_obj
 = v_res_4650_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0___boxed(lean_object* v_00_u03b3_4651_, lean_object* v_00_u03b1_4652_, lean_object* v_f_4653_, lean_object* v_positions_4654_, lean_object* v_ys_4655_, lean_object* v_xs_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l_Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0(v_00_u03b3_4651_, v_00_u03b1_4652_, v_f_4653_, v_positions_4654_, v_ys_4655_, v_xs_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec_ref(v_xs_4656_);
lean_dec_ref(v_ys_4655_);
lean_dec_ref(v_positions_4654_);
return v_res_4662_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_object* v_00_u03b1_4663_, lean_object* v_00_u03b3_4664_, lean_object* v_xs_4665_, lean_object* v_f_4666_, lean_object* v_as_4667_, lean_object* v_bs_4668_, lean_object* v_i_4669_, lean_object* v_cs_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___redArg(v_xs_4665_, v_f_4666_, v_as_4667_, v_bs_4668_, v_i_4669_, v_cs_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
return v___x_4676_;
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_4665_ = stack[2].m_obj;
lean_object* v_f_4666_ = stack[3].m_obj;
lean_object* v_as_4667_ = stack[4].m_obj;
lean_object* v_bs_4668_ = stack[5].m_obj;
lean_object* v_i_4669_ = stack[6].m_obj;
lean_object* v_cs_4670_ = stack[7].m_obj;
lean_object* v___y_4671_ = stack[8].m_obj;
lean_object* v___y_4672_ = stack[9].m_obj;
lean_object* v___y_4673_ = stack[10].m_obj;
lean_object* v___y_4674_ = stack[11].m_obj;
lean_object* v_res_4677_;
v_res_4677_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(lean_box(0), lean_box(0), v_xs_4665_, v_f_4666_, v_as_4667_, v_bs_4668_, v_i_4669_, v_cs_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_);
stack->m_obj
 = v_res_4677_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2___boxed(lean_object* v_00_u03b1_4678_, lean_object* v_00_u03b3_4679_, lean_object* v_xs_4680_, lean_object* v_f_4681_, lean_object* v_as_4682_, lean_object* v_bs_4683_, lean_object* v_i_4684_, lean_object* v_cs_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Array_zipWithMAux___at___00Lean_Elab_Structural_Positions_mapMwith___at___00Lean_Elab_Structural_mkBRecOnConst_spec__0_spec__2(v_00_u03b1_4678_, v_00_u03b3_4679_, v_xs_4680_, v_f_4681_, v_as_4682_, v_bs_4683_, v_i_4684_, v_cs_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec_ref(v_bs_4683_);
lean_dec_ref(v_as_4682_);
lean_dec_ref(v_xs_4680_);
return v_res_4691_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(lean_object* v_type_4692_, lean_object* v_maxFVars_x3f_4693_, lean_object* v_k_4694_, uint8_t v_cleanupAnnotations_4695_, uint8_t v_whnfType_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___f_4702_; lean_object* v___x_4703_; 
v___f_4702_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_toBelowAux_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4702_, 0, v_k_4694_);
v___x_4703_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_4692_, v_maxFVars_x3f_4693_, v___f_4702_, v_cleanupAnnotations_4695_, v_whnfType_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
v_a_4712_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4703_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4703_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4692_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_4693_ = stack[1].m_obj;
lean_object* v_k_4694_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_4695_ = stack[3].m_num;
uint8_t v_whnfType_4696_ = stack[4].m_num;
lean_object* v___y_4697_ = stack[5].m_obj;
lean_object* v___y_4698_ = stack[6].m_obj;
lean_object* v___y_4699_ = stack[7].m_obj;
lean_object* v___y_4700_ = stack[8].m_obj;
lean_object* v_res_4720_;
v_res_4720_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4692_, v_maxFVars_x3f_4693_, v_k_4694_, v_cleanupAnnotations_4695_, v_whnfType_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
stack->m_obj
 = v_res_4720_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg___boxed(lean_object* v_type_4721_, lean_object* v_maxFVars_x3f_4722_, lean_object* v_k_4723_, lean_object* v_cleanupAnnotations_4724_, lean_object* v_whnfType_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4731_; uint8_t v_whnfType_boxed_4732_; lean_object* v_res_4733_; 
v_cleanupAnnotations_boxed_4731_ = lean_unbox(v_cleanupAnnotations_4724_);
v_whnfType_boxed_4732_ = lean_unbox(v_whnfType_4725_);
v_res_4733_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4721_, v_maxFVars_x3f_4722_, v_k_4723_, v_cleanupAnnotations_boxed_4731_, v_whnfType_boxed_4732_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
return v_res_4733_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_object* v_00_u03b1_4734_, lean_object* v_type_4735_, lean_object* v_maxFVars_x3f_4736_, lean_object* v_k_4737_, uint8_t v_cleanupAnnotations_4738_, uint8_t v_whnfType_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
_start:
{
lean_object* v___x_4745_; 
v___x_4745_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_type_4735_, v_maxFVars_x3f_4736_, v_k_4737_, v_cleanupAnnotations_4738_, v_whnfType_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
return v___x_4745_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_4735_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_4736_ = stack[2].m_obj;
lean_object* v_k_4737_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_4738_ = stack[4].m_num;
uint8_t v_whnfType_4739_ = stack[5].m_num;
lean_object* v___y_4740_ = stack[6].m_obj;
lean_object* v___y_4741_ = stack[7].m_obj;
lean_object* v___y_4742_ = stack[8].m_obj;
lean_object* v___y_4743_ = stack[9].m_obj;
lean_object* v_res_4746_;
v_res_4746_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(lean_box(0), v_type_4735_, v_maxFVars_x3f_4736_, v_k_4737_, v_cleanupAnnotations_4738_, v_whnfType_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_);
stack->m_obj
 = v_res_4746_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___boxed(lean_object* v_00_u03b1_4747_, lean_object* v_type_4748_, lean_object* v_maxFVars_x3f_4749_, lean_object* v_k_4750_, lean_object* v_cleanupAnnotations_4751_, lean_object* v_whnfType_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_4758_; uint8_t v_whnfType_boxed_4759_; lean_object* v_res_4760_; 
v_cleanupAnnotations_boxed_4758_ = lean_unbox(v_cleanupAnnotations_4751_);
v_whnfType_boxed_4759_ = lean_unbox(v_whnfType_4752_);
v_res_4760_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1(v_00_u03b1_4747_, v_type_4748_, v_maxFVars_x3f_4749_, v_k_4750_, v_cleanupAnnotations_boxed_4758_, v_whnfType_boxed_4759_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
return v_res_4760_;
}
}
lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(lean_object* v_numTypeFormers_4761_, lean_object* v_x_4762_, lean_object* v_brecOnType_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v___x_4769_; 
v___x_4769_ = l_Lean_Meta_arrowDomainsN(v_numTypeFormers_4761_, v_brecOnType_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
return v___x_4769_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_numTypeFormers_4761_ = stack[0].m_obj;
lean_object* v_x_4762_ = stack[1].m_obj;
lean_object* v_brecOnType_4763_ = stack[2].m_obj;
lean_object* v___y_4764_ = stack[3].m_obj;
lean_object* v___y_4765_ = stack[4].m_obj;
lean_object* v___y_4766_ = stack[5].m_obj;
lean_object* v___y_4767_ = stack[6].m_obj;
lean_object* v_res_4770_;
v_res_4770_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(v_numTypeFormers_4761_, v_x_4762_, v_brecOnType_4763_, v___y_4764_, v___y_4765_, v___y_4766_, v___y_4767_);
stack->m_obj
 = v_res_4770_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed(lean_object* v_numTypeFormers_4771_, lean_object* v_x_4772_, lean_object* v_brecOnType_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0(v_numTypeFormers_4771_, v_x_4772_, v_brecOnType_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
lean_dec_ref(v_x_4772_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1(lean_object* v___x_4780_, lean_object* v_e_4781_){
_start:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; 
v___x_4782_ = l_Lean_indentD(v_e_4781_);
v___x_4783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4783_, 0, v___x_4780_);
lean_ctor_set(v___x_4783_, 1, v___x_4782_);
return v___x_4783_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(lean_object* v_a_4784_, lean_object* v_as_4785_, size_t v_sz_4786_, size_t v_i_4787_, lean_object* v_b_4788_){
_start:
{
uint8_t v___x_4790_; 
v___x_4790_ = lean_usize_dec_lt(v_i_4787_, v_sz_4786_);
if (v___x_4790_ == 0)
{
lean_object* v___x_4791_; 
lean_dec_ref(v_a_4784_);
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_b_4788_);
return v___x_4791_;
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4793_; size_t v___x_4794_; size_t v___x_4795_; 
v_a_4792_ = lean_array_uget_borrowed(v_as_4785_, v_i_4787_);
lean_inc_ref(v_a_4784_);
v___x_4793_ = lean_array_set(v_b_4788_, v_a_4792_, v_a_4784_);
v___x_4794_ = ((size_t)1ULL);
v___x_4795_ = lean_usize_add(v_i_4787_, v___x_4794_);
v_i_4787_ = v___x_4795_;
v_b_4788_ = v___x_4793_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4784_ = stack[0].m_obj;
lean_object* v_as_4785_ = stack[1].m_obj;
size_t v_sz_4786_ = stack[2].m_num;
size_t v_i_4787_ = stack[3].m_num;
lean_object* v_b_4788_ = stack[4].m_obj;
lean_object* v_res_4797_;
v_res_4797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4784_, v_as_4785_, v_sz_4786_, v_i_4787_, v_b_4788_);
stack->m_obj
 = v_res_4797_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg___boxed(lean_object* v_a_4798_, lean_object* v_as_4799_, lean_object* v_sz_4800_, lean_object* v_i_4801_, lean_object* v_b_4802_, lean_object* v___y_4803_){
_start:
{
size_t v_sz_boxed_4804_; size_t v_i_boxed_4805_; lean_object* v_res_4806_; 
v_sz_boxed_4804_ = lean_unbox_usize(v_sz_4800_);
lean_dec(v_sz_4800_);
v_i_boxed_4805_ = lean_unbox_usize(v_i_4801_);
lean_dec(v_i_4801_);
v_res_4806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4798_, v_as_4799_, v_sz_boxed_4804_, v_i_boxed_4805_, v_b_4802_);
lean_dec_ref(v_as_4799_);
return v_res_4806_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(lean_object* v_as_4807_, size_t v_sz_4808_, size_t v_i_4809_, lean_object* v_b_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_){
_start:
{
uint8_t v___x_4816_; 
v___x_4816_ = lean_usize_dec_lt(v_i_4809_, v_sz_4808_);
if (v___x_4816_ == 0)
{
lean_object* v___x_4817_; 
v___x_4817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4817_, 0, v_b_4810_);
return v___x_4817_;
}
else
{
lean_object* v_snd_4818_; lean_object* v_fst_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4863_; 
v_snd_4818_ = lean_ctor_get(v_b_4810_, 1);
v_fst_4819_ = lean_ctor_get(v_b_4810_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v_b_4810_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4821_ = v_b_4810_;
v_isShared_4822_ = v_isSharedCheck_4863_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_snd_4818_);
lean_inc(v_fst_4819_);
lean_dec(v_b_4810_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4863_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v_array_4823_; lean_object* v_start_4824_; lean_object* v_stop_4825_; uint8_t v___x_4826_; 
v_array_4823_ = lean_ctor_get(v_snd_4818_, 0);
v_start_4824_ = lean_ctor_get(v_snd_4818_, 1);
v_stop_4825_ = lean_ctor_get(v_snd_4818_, 2);
v___x_4826_ = lean_nat_dec_lt(v_start_4824_, v_stop_4825_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4828_; 
if (v_isShared_4822_ == 0)
{
v___x_4828_ = v___x_4821_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_fst_4819_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_snd_4818_);
v___x_4828_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4829_; 
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
return v___x_4829_;
}
}
else
{
lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4859_; 
lean_inc(v_stop_4825_);
lean_inc(v_start_4824_);
lean_inc_ref(v_array_4823_);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_snd_4818_);
if (v_isSharedCheck_4859_ == 0)
{
lean_object* v_unused_4860_; lean_object* v_unused_4861_; lean_object* v_unused_4862_; 
v_unused_4860_ = lean_ctor_get(v_snd_4818_, 2);
lean_dec(v_unused_4860_);
v_unused_4861_ = lean_ctor_get(v_snd_4818_, 1);
lean_dec(v_unused_4861_);
v_unused_4862_ = lean_ctor_get(v_snd_4818_, 0);
lean_dec(v_unused_4862_);
v___x_4832_ = v_snd_4818_;
v_isShared_4833_ = v_isSharedCheck_4859_;
goto v_resetjp_4831_;
}
else
{
lean_dec(v_snd_4818_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4859_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v_a_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4839_; 
v_a_4834_ = lean_array_uget_borrowed(v_as_4807_, v_i_4809_);
v___x_4835_ = lean_array_fget(v_array_4823_, v_start_4824_);
v___x_4836_ = lean_unsigned_to_nat(1u);
v___x_4837_ = lean_nat_add(v_start_4824_, v___x_4836_);
lean_dec(v_start_4824_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 1, v___x_4837_);
v___x_4839_ = v___x_4832_;
goto v_reusejp_4838_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_array_4823_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v___x_4837_);
lean_ctor_set(v_reuseFailAlloc_4858_, 2, v_stop_4825_);
v___x_4839_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4838_;
}
v_reusejp_4838_:
{
size_t v_sz_4840_; size_t v___x_4841_; lean_object* v___x_4842_; 
v_sz_4840_ = lean_array_size(v___x_4835_);
v___x_4841_ = ((size_t)0ULL);
lean_inc(v_a_4834_);
v___x_4842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4834_, v___x_4835_, v_sz_4840_, v___x_4841_, v_fst_4819_);
lean_dec(v___x_4835_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4845_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref_known(v___x_4842_, 1);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 1, v___x_4839_);
lean_ctor_set(v___x_4821_, 0, v_a_4843_);
v___x_4845_ = v___x_4821_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4843_);
lean_ctor_set(v_reuseFailAlloc_4849_, 1, v___x_4839_);
v___x_4845_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
size_t v___x_4846_; size_t v___x_4847_; 
v___x_4846_ = ((size_t)1ULL);
v___x_4847_ = lean_usize_add(v_i_4809_, v___x_4846_);
v_i_4809_ = v___x_4847_;
v_b_4810_ = v___x_4845_;
goto _start;
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec_ref(v___x_4839_);
lean_del_object(v___x_4821_);
v_a_4850_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4842_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4842_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_4807_ = stack[0].m_obj;
size_t v_sz_4808_ = stack[1].m_num;
size_t v_i_4809_ = stack[2].m_num;
lean_object* v_b_4810_ = stack[3].m_obj;
lean_object* v___y_4811_ = stack[4].m_obj;
lean_object* v___y_4812_ = stack[5].m_obj;
lean_object* v___y_4813_ = stack[6].m_obj;
lean_object* v___y_4814_ = stack[7].m_obj;
lean_object* v_res_4864_;
v_res_4864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_as_4807_, v_sz_4808_, v_i_4809_, v_b_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
stack->m_obj
 = v_res_4864_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2___boxed(lean_object* v_as_4865_, lean_object* v_sz_4866_, lean_object* v_i_4867_, lean_object* v_b_4868_, lean_object* v___y_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
size_t v_sz_boxed_4874_; size_t v_i_boxed_4875_; lean_object* v_res_4876_; 
v_sz_boxed_4874_ = lean_unbox_usize(v_sz_4866_);
lean_dec(v_sz_4866_);
v_i_boxed_4875_ = lean_unbox_usize(v_i_4867_);
lean_dec(v_i_4867_);
v_res_4876_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_as_4865_, v_sz_boxed_4874_, v_i_boxed_4875_, v_b_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec_ref(v_as_4865_);
return v_res_4876_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1(void){
_start:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = ((lean_object*)(l_Lean_Elab_Structural_inferBRecOnFTypes___closed__0));
v___x_4879_ = l_Lean_stringToMessageData(v___x_4878_);
return v___x_4879_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2(void){
_start:
{
lean_object* v___x_4880_; lean_object* v___f_4881_; 
v___x_4880_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__1);
v___f_4881_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__1), 2, 1);
lean_closure_set(v___f_4881_, 0, v___x_4880_);
return v___f_4881_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3(void){
_start:
{
lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4882_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnConst___closed__1, &l_Lean_Elab_Structural_mkBRecOnConst___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnConst___closed__1);
v___x_4883_ = l_Lean_Expr_sort___override(v___x_4882_);
return v___x_4883_;
}
}
lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object* v_recArgInfos_4884_, lean_object* v_positions_4885_, lean_object* v_brecOnConst_4886_, lean_object* v_a_4887_, lean_object* v_a_4888_, lean_object* v_a_4889_, lean_object* v_a_4890_){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v_recArgInfo_4894_; lean_object* v_indicesPos_4895_; lean_object* v_indIdx_4896_; lean_object* v_numTypeFormers_4897_; lean_object* v___f_4898_; lean_object* v_brecOn_4899_; lean_object* v___f_4900_; uint8_t v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4892_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
v___x_4893_ = lean_unsigned_to_nat(0u);
v_recArgInfo_4894_ = lean_array_get_borrowed(v___x_4892_, v_recArgInfos_4884_, v___x_4893_);
v_indicesPos_4895_ = lean_ctor_get(v_recArgInfo_4894_, 3);
v_indIdx_4896_ = lean_ctor_get(v_recArgInfo_4894_, 5);
v_numTypeFormers_4897_ = lean_array_get_size(v_positions_4885_);
v___f_4898_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_inferBRecOnFTypes___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4898_, 0, v_numTypeFormers_4897_);
lean_inc(v_indIdx_4896_);
v_brecOn_4899_ = lean_apply_1(v_brecOnConst_4886_, v_indIdx_4896_);
v___f_4900_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__2);
v___x_4901_ = 0;
v___x_4902_ = lean_box(v___x_4901_);
lean_inc_ref(v_brecOn_4899_);
v___x_4903_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_4903_, 0, v_brecOn_4899_);
lean_closure_set(v___x_4903_, 1, v___x_4902_);
v___x_4904_ = l_Lean_Meta_mapErrorImp___redArg(v___x_4903_, v___f_4900_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v___x_4905_; 
lean_dec_ref_known(v___x_4904_, 1);
lean_inc(v_a_4890_);
lean_inc_ref(v_a_4889_);
lean_inc(v_a_4888_);
lean_inc_ref(v_a_4887_);
v___x_4905_ = lean_infer_type(v_brecOn_4899_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_a_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; uint8_t v___x_4911_; lean_object* v___x_4912_; 
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
lean_inc(v_a_4906_);
lean_dec_ref_known(v___x_4905_, 1);
v___x_4907_ = lean_array_get_size(v_indicesPos_4895_);
v___x_4908_ = lean_unsigned_to_nat(1u);
v___x_4909_ = lean_nat_add(v___x_4907_, v___x_4908_);
v___x_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
v___x_4911_ = 0;
v___x_4912_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__1___redArg(v_a_4906_, v___x_4910_, v___f_4898_, v___x_4911_, v___x_4911_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; size_t v_sz_4919_; size_t v___x_4920_; lean_object* v___x_4921_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
lean_inc(v_a_4913_);
lean_dec_ref_known(v___x_4912_, 1);
v___x_4914_ = l_Lean_Elab_Structural_Positions_numIndices(v_positions_4885_);
v___x_4915_ = lean_obj_once(&l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3, &l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3_once, _init_l_Lean_Elab_Structural_inferBRecOnFTypes___closed__3);
v___x_4916_ = lean_mk_array(v___x_4914_, v___x_4915_);
v___x_4917_ = l_Array_toSubarray___redArg(v_positions_4885_, v___x_4893_, v_numTypeFormers_4897_);
v___x_4918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4916_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
v_sz_4919_ = lean_array_size(v_a_4913_);
v___x_4920_ = ((size_t)0ULL);
v___x_4921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__2(v_a_4913_, v_sz_4919_, v___x_4920_, v___x_4918_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_);
lean_dec(v_a_4913_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4930_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4924_ = v___x_4921_;
v_isShared_4925_ = v_isSharedCheck_4930_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v___x_4921_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4930_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v_fst_4926_; lean_object* v___x_4928_; 
v_fst_4926_ = lean_ctor_get(v_a_4922_, 0);
lean_inc(v_fst_4926_);
lean_dec(v_a_4922_);
if (v_isShared_4925_ == 0)
{
lean_ctor_set(v___x_4924_, 0, v_fst_4926_);
v___x_4928_ = v___x_4924_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_fst_4926_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
else
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4938_; 
v_a_4931_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4933_ = v___x_4921_;
v_isShared_4934_ = v_isSharedCheck_4938_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v___x_4921_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4938_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4936_; 
if (v_isShared_4934_ == 0)
{
v___x_4936_ = v___x_4933_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
return v___x_4936_;
}
}
}
}
else
{
lean_dec_ref(v_positions_4885_);
return v___x_4912_;
}
}
else
{
lean_object* v_a_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4946_; 
lean_dec_ref(v___f_4898_);
lean_dec_ref(v_positions_4885_);
v_a_4939_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4946_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4946_ == 0)
{
v___x_4941_ = v___x_4905_;
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_a_4939_);
lean_dec(v___x_4905_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4946_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
lean_object* v___x_4944_; 
if (v_isShared_4942_ == 0)
{
v___x_4944_ = v___x_4941_;
goto v_reusejp_4943_;
}
else
{
lean_object* v_reuseFailAlloc_4945_; 
v_reuseFailAlloc_4945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4945_, 0, v_a_4939_);
v___x_4944_ = v_reuseFailAlloc_4945_;
goto v_reusejp_4943_;
}
v_reusejp_4943_:
{
return v___x_4944_;
}
}
}
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec_ref(v_brecOn_4899_);
lean_dec_ref(v___f_4898_);
lean_dec_ref(v_positions_4885_);
v_a_4947_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4904_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4904_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_inferBRecOnFTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfos_4884_ = stack[0].m_obj;
lean_object* v_positions_4885_ = stack[1].m_obj;
lean_object* v_brecOnConst_4886_ = stack[2].m_obj;
lean_object* v_a_4887_ = stack[3].m_obj;
lean_object* v_a_4888_ = stack[4].m_obj;
lean_object* v_a_4889_ = stack[5].m_obj;
lean_object* v_a_4890_ = stack[6].m_obj;
lean_object* v_res_4955_;
v_res_4955_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4884_, v_positions_4885_, v_brecOnConst_4886_, v_a_4887_, v_a_4888_, v_a_4889_, v_a_4890_);
stack->m_obj
 = v_res_4955_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes___boxed(lean_object* v_recArgInfos_4956_, lean_object* v_positions_4957_, lean_object* v_brecOnConst_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_){
_start:
{
lean_object* v_res_4964_; 
v_res_4964_ = l_Lean_Elab_Structural_inferBRecOnFTypes(v_recArgInfos_4956_, v_positions_4957_, v_brecOnConst_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec_ref(v_recArgInfos_4956_);
return v_res_4964_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(lean_object* v_a_4965_, lean_object* v_as_4966_, size_t v_sz_4967_, size_t v_i_4968_, lean_object* v_b_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v___x_4975_; 
v___x_4975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___redArg(v_a_4965_, v_as_4966_, v_sz_4967_, v_i_4968_, v_b_4969_);
return v___x_4975_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4965_ = stack[0].m_obj;
lean_object* v_as_4966_ = stack[1].m_obj;
size_t v_sz_4967_ = stack[2].m_num;
size_t v_i_4968_ = stack[3].m_num;
lean_object* v_b_4969_ = stack[4].m_obj;
lean_object* v___y_4970_ = stack[5].m_obj;
lean_object* v___y_4971_ = stack[6].m_obj;
lean_object* v___y_4972_ = stack[7].m_obj;
lean_object* v___y_4973_ = stack[8].m_obj;
lean_object* v_res_4976_;
v_res_4976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4965_, v_as_4966_, v_sz_4967_, v_i_4968_, v_b_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
stack->m_obj
 = v_res_4976_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0___boxed(lean_object* v_a_4977_, lean_object* v_as_4978_, lean_object* v_sz_4979_, lean_object* v_i_4980_, lean_object* v_b_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
size_t v_sz_boxed_4987_; size_t v_i_boxed_4988_; lean_object* v_res_4989_; 
v_sz_boxed_4987_ = lean_unbox_usize(v_sz_4979_);
lean_dec(v_sz_4979_);
v_i_boxed_4988_ = lean_unbox_usize(v_i_4980_);
lean_dec(v_i_4980_);
v_res_4989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_inferBRecOnFTypes_spec__0(v_a_4977_, v_as_4978_, v_sz_boxed_4987_, v_i_boxed_4988_, v_b_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_);
lean_dec(v___y_4985_);
lean_dec_ref(v___y_4984_);
lean_dec(v___y_4983_);
lean_dec_ref(v___y_4982_);
lean_dec_ref(v_as_4978_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(lean_object* v_a_4990_, lean_object* v_a_4991_){
_start:
{
if (lean_obj_tag(v_a_4990_) == 0)
{
lean_object* v___x_4992_; 
v___x_4992_ = l_List_reverse___redArg(v_a_4991_);
return v___x_4992_;
}
else
{
lean_object* v_head_4993_; lean_object* v_tail_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5005_; 
v_head_4993_ = lean_ctor_get(v_a_4990_, 0);
v_tail_4994_ = lean_ctor_get(v_a_4990_, 1);
v_isSharedCheck_5005_ = !lean_is_exclusive(v_a_4990_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4996_ = v_a_4990_;
v_isShared_4997_ = v_isSharedCheck_5005_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_tail_4994_);
lean_inc(v_head_4993_);
lean_dec(v_a_4990_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5005_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5002_; 
v___x_4998_ = l_Nat_reprFast(v_head_4993_);
v___x_4999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4998_);
v___x_5000_ = l_Lean_MessageData_ofFormat(v___x_4999_);
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 1, v_a_4991_);
lean_ctor_set(v___x_4996_, 0, v___x_5000_);
v___x_5002_ = v___x_4996_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5004_, 0, v___x_5000_);
lean_ctor_set(v_reuseFailAlloc_5004_, 1, v_a_4991_);
v___x_5002_ = v_reuseFailAlloc_5004_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
v_a_4990_ = v_tail_4994_;
v_a_4991_ = v___x_5002_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
if (lean_obj_tag(v_a_5006_) == 0)
{
lean_object* v___x_5008_; 
v___x_5008_ = l_List_reverse___redArg(v_a_5007_);
return v___x_5008_;
}
else
{
lean_object* v_head_5009_; lean_object* v_tail_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5022_; 
v_head_5009_ = lean_ctor_get(v_a_5006_, 0);
v_tail_5010_ = lean_ctor_get(v_a_5006_, 1);
v_isSharedCheck_5022_ = !lean_is_exclusive(v_a_5006_);
if (v_isSharedCheck_5022_ == 0)
{
v___x_5012_ = v_a_5006_;
v_isShared_5013_ = v_isSharedCheck_5022_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_tail_5010_);
lean_inc(v_head_5009_);
lean_dec(v_a_5006_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5022_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5014_ = lean_array_to_list(v_head_5009_);
v___x_5015_ = lean_box(0);
v___x_5016_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__0(v___x_5014_, v___x_5015_);
v___x_5017_ = l_Lean_MessageData_ofList(v___x_5016_);
if (v_isShared_5013_ == 0)
{
lean_ctor_set(v___x_5012_, 1, v_a_5007_);
lean_ctor_set(v___x_5012_, 0, v___x_5017_);
v___x_5019_ = v___x_5012_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5021_; 
v_reuseFailAlloc_5021_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5017_);
lean_ctor_set(v_reuseFailAlloc_5021_, 1, v_a_5007_);
v___x_5019_ = v_reuseFailAlloc_5021_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
v_a_5006_ = v_tail_5010_;
v_a_5007_ = v___x_5019_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(lean_object* v_xs_5023_, lean_object* v_v_5024_, lean_object* v_i_5025_){
_start:
{
lean_object* v___x_5026_; uint8_t v___x_5027_; 
v___x_5026_ = lean_array_get_size(v_xs_5023_);
v___x_5027_ = lean_nat_dec_lt(v_i_5025_, v___x_5026_);
if (v___x_5027_ == 0)
{
lean_object* v___x_5028_; 
lean_dec(v_i_5025_);
v___x_5028_ = lean_box(0);
return v___x_5028_;
}
else
{
lean_object* v___x_5029_; uint8_t v___x_5030_; 
v___x_5029_ = lean_array_fget_borrowed(v_xs_5023_, v_i_5025_);
v___x_5030_ = lean_nat_dec_eq(v___x_5029_, v_v_5024_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = lean_unsigned_to_nat(1u);
v___x_5032_ = lean_nat_add(v_i_5025_, v___x_5031_);
lean_dec(v_i_5025_);
v_i_5025_ = v___x_5032_;
goto _start;
}
else
{
lean_object* v___x_5034_; 
v___x_5034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5034_, 0, v_i_5025_);
return v___x_5034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2___boxed(lean_object* v_xs_5035_, lean_object* v_v_5036_, lean_object* v_i_5037_){
_start:
{
lean_object* v_res_5038_; 
v_res_5038_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_5035_, v_v_5036_, v_i_5037_);
lean_dec(v_v_5036_);
lean_dec_ref(v_xs_5035_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(lean_object* v_xs_5039_, lean_object* v_v_5040_){
_start:
{
lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5041_ = lean_unsigned_to_nat(0u);
v___x_5042_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2_spec__2(v_xs_5039_, v_v_5040_, v___x_5041_);
return v___x_5042_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2___boxed(lean_object* v_xs_5043_, lean_object* v_v_5044_){
_start:
{
lean_object* v_res_5045_; 
v_res_5045_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_xs_5043_, v_v_5044_);
lean_dec(v_v_5044_);
lean_dec_ref(v_xs_5043_);
return v_res_5045_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(lean_object* v_fnIdx_5049_, lean_object* v_as_5050_, size_t v_sz_5051_, size_t v_i_5052_, lean_object* v_b_5053_){
_start:
{
uint8_t v___x_5054_; 
v___x_5054_ = lean_usize_dec_lt(v_i_5052_, v_sz_5051_);
if (v___x_5054_ == 0)
{
lean_inc_ref(v_b_5053_);
return v_b_5053_;
}
else
{
lean_object* v___x_5055_; lean_object* v_a_5056_; lean_object* v___x_5057_; 
v___x_5055_ = lean_box(0);
v_a_5056_ = lean_array_uget_borrowed(v_as_5050_, v_i_5052_);
v___x_5057_ = l_Array_finIdxOf_x3f___at___00Lean_Elab_Structural_mkBRecOnApp_spec__2(v_a_5056_, v_fnIdx_5049_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v___x_5058_; size_t v___x_5059_; size_t v___x_5060_; 
v___x_5058_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v___x_5059_ = ((size_t)1ULL);
v___x_5060_ = lean_usize_add(v_i_5052_, v___x_5059_);
v_i_5052_ = v___x_5060_;
v_b_5053_ = v___x_5058_;
goto _start;
}
else
{
lean_object* v_val_5062_; lean_object* v___x_5064_; uint8_t v_isShared_5065_; uint8_t v_isSharedCheck_5073_; 
v_val_5062_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5073_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5073_ == 0)
{
v___x_5064_ = v___x_5057_;
v_isShared_5065_ = v_isSharedCheck_5073_;
goto v_resetjp_5063_;
}
else
{
lean_inc(v_val_5062_);
lean_dec(v___x_5057_);
v___x_5064_ = lean_box(0);
v_isShared_5065_ = v_isSharedCheck_5073_;
goto v_resetjp_5063_;
}
v_resetjp_5063_:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5069_; 
v___x_5066_ = lean_array_get_size(v_a_5056_);
v___x_5067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
lean_ctor_set(v___x_5067_, 1, v_val_5062_);
if (v_isShared_5065_ == 0)
{
lean_ctor_set(v___x_5064_, 0, v___x_5067_);
v___x_5069_ = v___x_5064_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5072_; 
v_reuseFailAlloc_5072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5072_, 0, v___x_5067_);
v___x_5069_ = v_reuseFailAlloc_5072_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; 
v___x_5070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5069_);
v___x_5071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5071_, 0, v___x_5070_);
lean_ctor_set(v___x_5071_, 1, v___x_5055_);
return v___x_5071_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_fnIdx_5049_ = stack[0].m_obj;
lean_object* v_as_5050_ = stack[1].m_obj;
size_t v_sz_5051_ = stack[2].m_num;
size_t v_i_5052_ = stack[3].m_num;
lean_object* v_b_5053_ = stack[4].m_obj;
lean_object* v_res_5074_;
v_res_5074_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5049_, v_as_5050_, v_sz_5051_, v_i_5052_, v_b_5053_);
stack->m_obj
 = v_res_5074_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___boxed(lean_object* v_fnIdx_5075_, lean_object* v_as_5076_, lean_object* v_sz_5077_, lean_object* v_i_5078_, lean_object* v_b_5079_){
_start:
{
size_t v_sz_boxed_5080_; size_t v_i_boxed_5081_; lean_object* v_res_5082_; 
v_sz_boxed_5080_ = lean_unbox_usize(v_sz_5077_);
lean_dec(v_sz_5077_);
v_i_boxed_5081_ = lean_unbox_usize(v_i_5078_);
lean_dec(v_i_5078_);
v_res_5082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5075_, v_as_5076_, v_sz_boxed_5080_, v_i_boxed_5081_, v_b_5079_);
lean_dec_ref(v_b_5079_);
lean_dec_ref(v_as_5076_);
lean_dec(v_fnIdx_5075_);
return v_res_5082_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5084_ = ((lean_object*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__0));
v___x_5085_ = l_Lean_stringToMessageData(v___x_5084_);
return v___x_5085_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0(lean_object* v_recArgInfo_5086_, lean_object* v_positions_5087_, lean_object* v_fnIdx_5088_, lean_object* v_brecOnConst_5089_, lean_object* v_packedFArgs_5090_, lean_object* v_funTypes_5091_, lean_object* v_ys_5092_, lean_object* v___value_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v___x_5113_; lean_object* v_fst_5114_; lean_object* v_snd_5115_; lean_object* v___x_5116_; size_t v_sz_5117_; size_t v___x_5118_; lean_object* v___x_5119_; lean_object* v_fst_5120_; 
lean_inc_ref(v_ys_5092_);
lean_inc_ref(v_recArgInfo_5086_);
v___x_5113_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_5086_, v_ys_5092_);
v_fst_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_fst_5114_);
v_snd_5115_ = lean_ctor_get(v___x_5113_, 1);
lean_inc(v_snd_5115_);
lean_dec_ref(v___x_5113_);
v___x_5116_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3___closed__0));
v_sz_5117_ = lean_array_size(v_positions_5087_);
v___x_5118_ = ((size_t)0ULL);
v___x_5119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__3(v_fnIdx_5088_, v_positions_5087_, v_sz_5117_, v___x_5118_, v___x_5116_);
v_fst_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc(v_fst_5120_);
lean_dec_ref(v___x_5119_);
if (lean_obj_tag(v_fst_5120_) == 0)
{
lean_dec(v_snd_5115_);
lean_dec(v_fst_5114_);
lean_dec_ref(v_ys_5092_);
lean_dec_ref(v_brecOnConst_5089_);
lean_dec_ref(v_recArgInfo_5086_);
goto v___jp_5099_;
}
else
{
lean_object* v_val_5121_; 
v_val_5121_ = lean_ctor_get(v_fst_5120_, 0);
lean_inc(v_val_5121_);
lean_dec_ref_known(v_fst_5120_, 1);
if (lean_obj_tag(v_val_5121_) == 1)
{
lean_object* v_val_5122_; lean_object* v_fst_5123_; lean_object* v_snd_5124_; lean_object* v_indIdx_5125_; lean_object* v_brecOn_5126_; lean_object* v_brecOn_5127_; lean_object* v_brecOn_5128_; lean_object* v___x_5129_; 
lean_dec(v_fnIdx_5088_);
lean_dec_ref(v_positions_5087_);
v_val_5122_ = lean_ctor_get(v_val_5121_, 0);
lean_inc(v_val_5122_);
lean_dec_ref_known(v_val_5121_, 1);
v_fst_5123_ = lean_ctor_get(v_val_5122_, 0);
lean_inc(v_fst_5123_);
v_snd_5124_ = lean_ctor_get(v_val_5122_, 1);
lean_inc(v_snd_5124_);
lean_dec(v_val_5122_);
v_indIdx_5125_ = lean_ctor_get(v_recArgInfo_5086_, 5);
lean_inc(v_indIdx_5125_);
lean_dec_ref(v_recArgInfo_5086_);
v_brecOn_5126_ = lean_apply_1(v_brecOnConst_5089_, v_indIdx_5125_);
v_brecOn_5127_ = l_Lean_mkAppN(v_brecOn_5126_, v_fst_5114_);
lean_dec(v_fst_5114_);
v_brecOn_5128_ = l_Lean_mkAppN(v_brecOn_5127_, v_packedFArgs_5090_);
v___x_5129_ = l_Lean_Meta_PProdN_projM(v_fst_5123_, v_snd_5124_, v_brecOn_5128_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec(v_snd_5124_);
lean_dec(v_fst_5123_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v___x_5131_; uint8_t v___x_5132_; uint8_t v___x_5133_; lean_object* v___x_5134_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v___x_5131_ = l_Lean_mkAppN(v_a_5130_, v_snd_5115_);
lean_dec(v_snd_5115_);
v___x_5132_ = 1;
v___x_5133_ = 1;
v___x_5134_ = l_Lean_Meta_mkLetFVars(v_funTypes_5091_, v___x_5131_, v___x_5132_, v___x_5132_, v___x_5133_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; uint8_t v___x_5136_; lean_object* v___x_5137_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5136_ = 0;
v___x_5137_ = l_Lean_Meta_mkLambdaFVars(v_ys_5092_, v_a_5135_, v___x_5136_, v___x_5132_, v___x_5136_, v___x_5132_, v___x_5133_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec_ref(v_ys_5092_);
return v___x_5137_;
}
else
{
lean_dec_ref(v_ys_5092_);
return v___x_5134_;
}
}
else
{
lean_dec(v_snd_5115_);
lean_dec_ref(v_ys_5092_);
return v___x_5129_;
}
}
else
{
lean_dec(v_val_5121_);
lean_dec(v_snd_5115_);
lean_dec(v_fst_5114_);
lean_dec_ref(v_ys_5092_);
lean_dec_ref(v_brecOnConst_5089_);
lean_dec_ref(v_recArgInfo_5086_);
goto v___jp_5099_;
}
}
v___jp_5099_:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; 
v___x_5100_ = lean_obj_once(&l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1, &l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1_once, _init_l_Lean_Elab_Structural_mkBRecOnApp___lam__0___closed__1);
v___x_5101_ = l_Nat_reprFast(v_fnIdx_5088_);
v___x_5102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5102_, 0, v___x_5101_);
v___x_5103_ = l_Lean_MessageData_ofFormat(v___x_5102_);
v___x_5104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5100_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
v___x_5105_ = lean_obj_once(&l_Lean_Elab_Structural_toBelow___lam__1___closed__3, &l_Lean_Elab_Structural_toBelow___lam__1___closed__3_once, _init_l_Lean_Elab_Structural_toBelow___lam__1___closed__3);
v___x_5106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5106_, 0, v___x_5104_);
lean_ctor_set(v___x_5106_, 1, v___x_5105_);
v___x_5107_ = lean_array_to_list(v_positions_5087_);
v___x_5108_ = lean_box(0);
v___x_5109_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_mkBRecOnApp_spec__1(v___x_5107_, v___x_5108_);
v___x_5110_ = l_Lean_MessageData_ofList(v___x_5109_);
v___x_5111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5111_, 0, v___x_5106_);
lean_ctor_set(v___x_5111_, 1, v___x_5110_);
v___x_5112_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_BRecOn_0__Lean_Elab_Structural_throwToBelowFailed_spec__0___redArg(v___x_5111_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
return v___x_5112_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnApp___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_recArgInfo_5086_ = stack[0].m_obj;
lean_object* v_positions_5087_ = stack[1].m_obj;
lean_object* v_fnIdx_5088_ = stack[2].m_obj;
lean_object* v_brecOnConst_5089_ = stack[3].m_obj;
lean_object* v_packedFArgs_5090_ = stack[4].m_obj;
lean_object* v_funTypes_5091_ = stack[5].m_obj;
lean_object* v_ys_5092_ = stack[6].m_obj;
lean_object* v___value_5093_ = stack[7].m_obj;
lean_object* v___y_5094_ = stack[8].m_obj;
lean_object* v___y_5095_ = stack[9].m_obj;
lean_object* v___y_5096_ = stack[10].m_obj;
lean_object* v___y_5097_ = stack[11].m_obj;
lean_object* v_res_5138_;
v_res_5138_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5086_, v_positions_5087_, v_fnIdx_5088_, v_brecOnConst_5089_, v_packedFArgs_5090_, v_funTypes_5091_, v_ys_5092_, v___value_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
stack->m_obj
 = v_res_5138_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed(lean_object* v_recArgInfo_5139_, lean_object* v_positions_5140_, lean_object* v_fnIdx_5141_, lean_object* v_brecOnConst_5142_, lean_object* v_packedFArgs_5143_, lean_object* v_funTypes_5144_, lean_object* v_ys_5145_, lean_object* v___value_5146_, lean_object* v___y_5147_, lean_object* v___y_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Lean_Elab_Structural_mkBRecOnApp___lam__0(v_recArgInfo_5139_, v_positions_5140_, v_fnIdx_5141_, v_brecOnConst_5142_, v_packedFArgs_5143_, v_funTypes_5144_, v_ys_5145_, v___value_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
lean_dec(v___y_5148_);
lean_dec_ref(v___y_5147_);
lean_dec_ref(v___value_5146_);
lean_dec_ref(v_funTypes_5144_);
lean_dec_ref(v_packedFArgs_5143_);
return v_res_5152_;
}
}
lean_object* l_Lean_Elab_Structural_mkBRecOnApp(lean_object* v_positions_5153_, lean_object* v_fnIdx_5154_, lean_object* v_brecOnConst_5155_, lean_object* v_packedFArgs_5156_, lean_object* v_funTypes_5157_, lean_object* v_recArgInfo_5158_, lean_object* v_value_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_){
_start:
{
lean_object* v___f_5165_; uint8_t v___x_5166_; lean_object* v___x_5167_; 
v___f_5165_ = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkBRecOnApp___lam__0___boxed), 13, 6);
lean_closure_set(v___f_5165_, 0, v_recArgInfo_5158_);
lean_closure_set(v___f_5165_, 1, v_positions_5153_);
lean_closure_set(v___f_5165_, 2, v_fnIdx_5154_);
lean_closure_set(v___f_5165_, 3, v_brecOnConst_5155_);
lean_closure_set(v___f_5165_, 4, v_packedFArgs_5156_);
lean_closure_set(v___f_5165_, 5, v_funTypes_5157_);
v___x_5166_ = 0;
v___x_5167_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_mkBRecOnMotive_spec__0___redArg(v_value_5159_, v___f_5165_, v___x_5166_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
return v___x_5167_;
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_mkBRecOnApp_0interp(lean_interpreter_value* stack)
{
lean_object* v_positions_5153_ = stack[0].m_obj;
lean_object* v_fnIdx_5154_ = stack[1].m_obj;
lean_object* v_brecOnConst_5155_ = stack[2].m_obj;
lean_object* v_packedFArgs_5156_ = stack[3].m_obj;
lean_object* v_funTypes_5157_ = stack[4].m_obj;
lean_object* v_recArgInfo_5158_ = stack[5].m_obj;
lean_object* v_value_5159_ = stack[6].m_obj;
lean_object* v_a_5160_ = stack[7].m_obj;
lean_object* v_a_5161_ = stack[8].m_obj;
lean_object* v_a_5162_ = stack[9].m_obj;
lean_object* v_a_5163_ = stack[10].m_obj;
lean_object* v_res_5168_;
v_res_5168_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5153_, v_fnIdx_5154_, v_brecOnConst_5155_, v_packedFArgs_5156_, v_funTypes_5157_, v_recArgInfo_5158_, v_value_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_);
stack->m_obj
 = v_res_5168_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkBRecOnApp___boxed(lean_object* v_positions_5169_, lean_object* v_fnIdx_5170_, lean_object* v_brecOnConst_5171_, lean_object* v_packedFArgs_5172_, lean_object* v_funTypes_5173_, lean_object* v_recArgInfo_5174_, lean_object* v_value_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_Elab_Structural_mkBRecOnApp(v_positions_5169_, v_fnIdx_5170_, v_brecOnConst_5171_, v_packedFArgs_5172_, v_funTypes_5173_, v_recArgInfo_5174_, v_value_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
lean_dec(v_a_5179_);
lean_dec_ref(v_a_5178_);
lean_dec(v_a_5177_);
lean_dec_ref(v_a_5176_);
return v_res_5181_;
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
