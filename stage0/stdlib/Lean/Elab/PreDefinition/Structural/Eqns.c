// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Eqns
// Imports: public import Lean.Elab.PreDefinition.FixedParams import Lean.Elab.PreDefinition.EqnsUtils import Lean.Meta.Tactic.CasesOnStuckLHS import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.Simp.Main import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.CasesOnStuckLHS import Lean.Meta.Tactic.Split
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
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t l_Lean_Environment_hasExposedBody(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_define(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
lean_object* l_Lean_Meta_withEqnOptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedFixedParamPerms_default;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2;
static const lean_array_object l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3 = (const lean_object*)&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo;
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "could not find `.brecOn` application in"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1;
static const lean_closure_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "goal not an equality"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "step:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "no progress at goal\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(83, 150, 182, 177, 14, 34, 156, 192)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "whnfReducibleLHS succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpMatch\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpIf\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "simpTargetStar closed the goal"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deltaRHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "casesOnStuckLHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "splitTarget\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "simpTargetStar modified the goal"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "tryContadiction succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tryURefl succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "theorem `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not an equality\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "abstracting"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " from"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "no theorem `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "goUnfold:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "proving:"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "failed to generate equational theorem for `"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 221, 148, 2, 30, 47, 242, 74)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 216, 81, 142, 241, 75, 113, 77)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_eqnInfoExt;
static lean_once_cell_t l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 185, 97, 74, 150, 8, 57, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 19, 250, 232, 19, 103, 59, 84)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 64, 85, 238, 73, 235, 224, 238)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 241, 197, 13, 174, 23, 186, 239)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(123, 232, 160, 88, 66, 78, 213, 243)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 117, 235, 94, 194, 72, 147, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 146, 13, 135, 45, 158, 59, 107)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 222, 70, 43, 201, 77, 119, 184)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 51, 79, 28, 160, 228, 197, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(130, 14, 83, 143, 58, 41, 180, 194)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 131, 204, 33, 154, 17, 78, 114)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 169, 96, 182, 175, 131, 16, 69)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(171, 31, 30, 186, 131, 197, 38, 7)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_9_ = l_Lean_Elab_instInhabitedFixedParamPerms_default;
v___x_10_ = ((lean_object*)(l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__3));
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2, &l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2_once, _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__2);
v___x_13_ = lean_box(0);
v___x_14_ = lean_box(0);
v___x_15_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_12_);
lean_ctor_set(v___x_15_, 3, v___x_12_);
lean_ctor_set(v___x_15_, 4, v___x_11_);
lean_ctor_set(v___x_15_, 5, v___x_10_);
lean_ctor_set(v___x_15_, 6, v___x_9_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4, &l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4_once, _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default___closed__4);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
return v___x_17_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(lean_object* v_k_18_, lean_object* v_b_19_, lean_object* v_c_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; 
lean_inc(v___y_24_);
lean_inc_ref(v___y_23_);
lean_inc(v___y_22_);
lean_inc_ref(v___y_21_);
v___x_26_ = lean_apply_7(v_k_18_, v_b_19_, v_c_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, lean_box(0));
return v___x_26_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_18_ = stack[0].m_obj;
lean_object* v_b_19_ = stack[1].m_obj;
lean_object* v_c_20_ = stack[2].m_obj;
lean_object* v___y_21_ = stack[3].m_obj;
lean_object* v___y_22_ = stack[4].m_obj;
lean_object* v___y_23_ = stack[5].m_obj;
lean_object* v___y_24_ = stack[6].m_obj;
lean_object* v_res_27_;
v_res_27_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(v_k_18_, v_b_19_, v_c_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_28_, lean_object* v_b_29_, lean_object* v_c_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(v_k_28_, v_b_29_, v_c_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_36_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(lean_object* v_type_37_, lean_object* v_k_38_, uint8_t v_cleanupAnnotations_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___f_45_; uint8_t v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___f_45_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_45_, 0, v_k_38_);
v___x_46_ = 0;
v___x_47_ = lean_box(0);
v___x_48_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_46_, v___x_47_, v_type_37_, v___f_45_, v_cleanupAnnotations_39_, v___x_46_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_48_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
v_a_57_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_48_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_48_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_37_ = stack[0].m_obj;
lean_object* v_k_38_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_39_ = stack[2].m_num;
lean_object* v___y_40_ = stack[3].m_obj;
lean_object* v___y_41_ = stack[4].m_obj;
lean_object* v___y_42_ = stack[5].m_obj;
lean_object* v___y_43_ = stack[6].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_type_37_, v_k_38_, v_cleanupAnnotations_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___boxed(lean_object* v_type_66_, lean_object* v_k_67_, lean_object* v_cleanupAnnotations_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_74_; lean_object* v_res_75_; 
v_cleanupAnnotations_boxed_74_ = lean_unbox(v_cleanupAnnotations_68_);
v_res_75_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_type_66_, v_k_67_, v_cleanupAnnotations_boxed_74_, v___y_69_, v___y_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_75_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(lean_object* v_00_u03b1_76_, lean_object* v_type_77_, lean_object* v_k_78_, uint8_t v_cleanupAnnotations_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_type_77_, v_k_78_, v_cleanupAnnotations_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_77_ = stack[1].m_obj;
lean_object* v_k_78_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_79_ = stack[3].m_num;
lean_object* v___y_80_ = stack[4].m_obj;
lean_object* v___y_81_ = stack[5].m_obj;
lean_object* v___y_82_ = stack[6].m_obj;
lean_object* v___y_83_ = stack[7].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(lean_box(0), v_type_77_, v_k_78_, v_cleanupAnnotations_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___boxed(lean_object* v_00_u03b1_87_, lean_object* v_type_88_, lean_object* v_k_89_, lean_object* v_cleanupAnnotations_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_96_; lean_object* v_res_97_; 
v_cleanupAnnotations_boxed_96_ = lean_unbox(v_cleanupAnnotations_90_);
v_res_97_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(v_00_u03b1_87_, v_type_88_, v_k_89_, v_cleanupAnnotations_boxed_96_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_97_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(lean_object* v___x_98_, lean_object* v_k_99_, lean_object* v___x_100_, lean_object* v_x_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = l_Subarray_copy___redArg(v___x_98_);
lean_inc_ref(v_x_101_);
v___x_108_ = l_Lean_mkAppN(v_x_101_, v___x_107_);
lean_dec_ref(v___x_107_);
lean_inc(v___y_105_);
lean_inc_ref(v___y_104_);
lean_inc(v___y_103_);
lean_inc_ref(v___y_102_);
v___x_109_ = lean_apply_8(v_k_99_, v___x_100_, v_x_101_, v___x_108_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_98_ = stack[0].m_obj;
lean_object* v_k_99_ = stack[1].m_obj;
lean_object* v___x_100_ = stack[2].m_obj;
lean_object* v_x_101_ = stack[3].m_obj;
lean_object* v___y_102_ = stack[4].m_obj;
lean_object* v___y_103_ = stack[5].m_obj;
lean_object* v___y_104_ = stack[6].m_obj;
lean_object* v___y_105_ = stack[7].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(v___x_98_, v_k_99_, v___x_100_, v_x_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed(lean_object* v___x_111_, lean_object* v_k_112_, lean_object* v___x_113_, lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(v___x_111_, v_k_112_, v___x_113_, v_x_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_120_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(lean_object* v_typeName_121_, lean_object* v_idx_122_, lean_object* v_x_123_, lean_object* v_k_124_, lean_object* v_brecOnApp_125_, lean_object* v_x_126_, lean_object* v_c_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = l_Lean_mkProj(v_typeName_121_, v_idx_122_, v_c_127_);
v___x_134_ = l_Lean_mkAppN(v___x_133_, v_x_123_);
lean_inc(v___y_131_);
lean_inc_ref(v___y_130_);
lean_inc(v___y_129_);
lean_inc_ref(v___y_128_);
v___x_135_ = lean_apply_8(v_k_124_, v_brecOnApp_125_, v_x_126_, v___x_134_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, lean_box(0));
return v___x_135_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_typeName_121_ = stack[0].m_obj;
lean_object* v_idx_122_ = stack[1].m_obj;
lean_object* v_x_123_ = stack[2].m_obj;
lean_object* v_k_124_ = stack[3].m_obj;
lean_object* v_brecOnApp_125_ = stack[4].m_obj;
lean_object* v_x_126_ = stack[5].m_obj;
lean_object* v_c_127_ = stack[6].m_obj;
lean_object* v___y_128_ = stack[7].m_obj;
lean_object* v___y_129_ = stack[8].m_obj;
lean_object* v___y_130_ = stack[9].m_obj;
lean_object* v___y_131_ = stack[10].m_obj;
lean_object* v_res_136_;
v_res_136_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(v_typeName_121_, v_idx_122_, v_x_123_, v_k_124_, v_brecOnApp_125_, v_x_126_, v_c_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed(lean_object* v_typeName_137_, lean_object* v_idx_138_, lean_object* v_x_139_, lean_object* v_k_140_, lean_object* v_brecOnApp_141_, lean_object* v_x_142_, lean_object* v_c_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(v_typeName_137_, v_idx_138_, v_x_139_, v_k_140_, v_brecOnApp_141_, v_x_142_, v_c_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec_ref(v_x_139_);
return v_res_149_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(lean_object* v_k_150_, lean_object* v_b_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
lean_inc(v___y_155_);
lean_inc_ref(v___y_154_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
v___x_157_ = lean_apply_6(v_k_150_, v_b_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, lean_box(0));
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_150_ = stack[0].m_obj;
lean_object* v_b_151_ = stack[1].m_obj;
lean_object* v___y_152_ = stack[2].m_obj;
lean_object* v___y_153_ = stack[3].m_obj;
lean_object* v___y_154_ = stack[4].m_obj;
lean_object* v___y_155_ = stack[5].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(v_k_150_, v_b_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_159_, lean_object* v_b_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(v_k_159_, v_b_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_166_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(lean_object* v_name_167_, uint8_t v_bi_168_, lean_object* v_type_169_, lean_object* v_k_170_, uint8_t v_kind_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; 
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_177_, 0, v_k_170_);
v___x_178_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_167_, v_bi_168_, v_type_169_, v___f_177_, v_kind_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_178_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_178_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_167_ = stack[0].m_obj;
uint8_t v_bi_168_ = stack[1].m_num;
lean_object* v_type_169_ = stack[2].m_obj;
lean_object* v_k_170_ = stack[3].m_obj;
uint8_t v_kind_171_ = stack[4].m_num;
lean_object* v___y_172_ = stack[5].m_obj;
lean_object* v___y_173_ = stack[6].m_obj;
lean_object* v___y_174_ = stack[7].m_obj;
lean_object* v___y_175_ = stack[8].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_167_, v_bi_168_, v_type_169_, v_k_170_, v_kind_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___boxed(lean_object* v_name_196_, lean_object* v_bi_197_, lean_object* v_type_198_, lean_object* v_k_199_, lean_object* v_kind_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
uint8_t v_bi_boxed_206_; uint8_t v_kind_boxed_207_; lean_object* v_res_208_; 
v_bi_boxed_206_ = lean_unbox(v_bi_197_);
v_kind_boxed_207_ = lean_unbox(v_kind_200_);
v_res_208_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_196_, v_bi_boxed_206_, v_type_198_, v_k_199_, v_kind_boxed_207_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_208_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(lean_object* v_name_209_, lean_object* v_type_210_, lean_object* v_k_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
uint8_t v___x_217_; uint8_t v___x_218_; lean_object* v___x_219_; 
v___x_217_ = 0;
v___x_218_ = 0;
v___x_219_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_209_, v___x_217_, v_type_210_, v_k_211_, v___x_218_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_209_ = stack[0].m_obj;
lean_object* v_type_210_ = stack[1].m_obj;
lean_object* v_k_211_ = stack[2].m_obj;
lean_object* v___y_212_ = stack[3].m_obj;
lean_object* v___y_213_ = stack[4].m_obj;
lean_object* v___y_214_ = stack[5].m_obj;
lean_object* v___y_215_ = stack[6].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v_name_209_, v_type_210_, v_k_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg___boxed(lean_object* v_name_221_, lean_object* v_type_222_, lean_object* v_k_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v_name_221_, v_type_222_, v_k_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(lean_object* v_msgData_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v_env_237_; uint8_t v___x_238_; lean_object* v_env_239_; lean_object* v___x_240_; lean_object* v_toCold_241_; lean_object* v_mctx_242_; lean_object* v_lctx_243_; lean_object* v_options_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_236_ = lean_st_ref_get(v___y_234_);
v_env_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc_ref(v_env_237_);
lean_dec(v___x_236_);
v___x_238_ = 0;
v_env_239_ = l_Lean_Environment_setRecordingDeps(v_env_237_, v___x_238_);
v___x_240_ = lean_st_ref_get(v___y_232_);
v_toCold_241_ = lean_ctor_get(v___y_233_, 0);
v_mctx_242_ = lean_ctor_get(v___x_240_, 0);
lean_inc_ref(v_mctx_242_);
lean_dec(v___x_240_);
v_lctx_243_ = lean_ctor_get(v___y_231_, 2);
v_options_244_ = lean_ctor_get(v_toCold_241_, 2);
lean_inc_ref(v_options_244_);
lean_inc_ref(v_lctx_243_);
v___x_245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_245_, 0, v_env_239_);
lean_ctor_set(v___x_245_, 1, v_mctx_242_);
lean_ctor_set(v___x_245_, 2, v_lctx_243_);
lean_ctor_set(v___x_245_, 3, v_options_244_);
v___x_246_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v_msgData_230_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_230_ = stack[0].m_obj;
lean_object* v___y_231_ = stack[1].m_obj;
lean_object* v___y_232_ = stack[2].m_obj;
lean_object* v___y_233_ = stack[3].m_obj;
lean_object* v___y_234_ = stack[4].m_obj;
lean_object* v_res_248_;
v_res_248_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msgData_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0___boxed(lean_object* v_msgData_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msgData_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_255_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_272_; 
v_ref_262_ = lean_ctor_get(v___y_259_, 2);
v___x_263_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_272_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_272_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
lean_inc(v_ref_262_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v_ref_262_);
lean_ctor_set(v___x_268_, 1, v_a_264_);
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 1);
lean_ctor_set(v___x_266_, 0, v___x_268_);
v___x_270_ = v___x_266_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_256_ = stack[0].m_obj;
lean_object* v___y_257_ = stack[1].m_obj;
lean_object* v___y_258_ = stack[2].m_obj;
lean_object* v___y_259_ = stack[3].m_obj;
lean_object* v___y_260_ = stack[4].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg___boxed(lean_object* v_msg_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_280_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(lean_object* v_xs_281_, lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_array_get_size(v_xs_281_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_281_ = stack[0].m_obj;
lean_object* v_x_282_ = stack[1].m_obj;
lean_object* v___y_283_ = stack[2].m_obj;
lean_object* v___y_284_ = stack[3].m_obj;
lean_object* v___y_285_ = stack[4].m_obj;
lean_object* v___y_286_ = stack[5].m_obj;
lean_object* v_res_290_;
v_res_290_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(v_xs_281_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed(lean_object* v_xs_291_, lean_object* v_x_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(v_xs_291_, v_x_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec_ref(v_x_292_);
lean_dec_ref(v_xs_291_);
return v_res_298_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_299_; lean_object* v_dummy_300_; 
v___x_299_ = lean_box(0);
v_dummy_300_ = l_Lean_Expr_sort___override(v___x_299_);
return v_dummy_300_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__0));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(lean_object* v_e_308_, lean_object* v_k_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; 
if (lean_obj_tag(v_x_310_) == 5)
{
lean_object* v_fn_327_; lean_object* v_arg_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_fn_327_ = lean_ctor_get(v_x_310_, 0);
lean_inc_ref(v_fn_327_);
v_arg_328_ = lean_ctor_get(v_x_310_, 1);
lean_inc_ref(v_arg_328_);
lean_dec_ref_known(v_x_310_, 2);
v___x_329_ = lean_array_set(v_x_311_, v_x_312_, v_arg_328_);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_sub(v_x_312_, v___x_330_);
lean_dec(v_x_312_);
v_x_310_ = v_fn_327_;
v_x_311_ = v___x_329_;
v_x_312_ = v___x_331_;
goto _start;
}
else
{
lean_dec(v_x_312_);
if (lean_obj_tag(v_x_310_) == 11)
{
lean_object* v_typeName_333_; lean_object* v_idx_334_; lean_object* v_struct_335_; lean_object* v___f_336_; lean_object* v___x_337_; 
lean_dec_ref(v_e_308_);
v_typeName_333_ = lean_ctor_get(v_x_310_, 0);
lean_inc(v_typeName_333_);
v_idx_334_ = lean_ctor_get(v_x_310_, 1);
lean_inc(v_idx_334_);
v_struct_335_ = lean_ctor_get(v_x_310_, 2);
lean_inc_ref(v_struct_335_);
lean_dec_ref_known(v_x_310_, 3);
v___f_336_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_336_, 0, v_typeName_333_);
lean_closure_set(v___f_336_, 1, v_idx_334_);
lean_closure_set(v___f_336_, 2, v_x_311_);
lean_closure_set(v___f_336_, 3, v_k_309_);
v___x_337_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_struct_335_, v___f_336_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
return v___x_337_;
}
else
{
if (lean_obj_tag(v_x_310_) == 4)
{
lean_object* v_declName_338_; lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v_env_341_; uint8_t v___x_342_; 
v_declName_338_ = lean_ctor_get(v_x_310_, 0);
v___f_339_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2));
v___x_340_ = lean_st_ref_get(v___y_316_);
v_env_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref(v_env_341_);
lean_dec(v___x_340_);
lean_inc(v_declName_338_);
v___x_342_ = l_Lean_isBRecOnRecursor(v_env_341_, v_declName_338_);
if (v___x_342_ == 0)
{
lean_dec_ref_known(v_x_310_, 2);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_k_309_);
v___y_319_ = v___y_313_;
v___y_320_ = v___y_314_;
v___y_321_ = v___y_315_;
v___y_322_ = v___y_316_;
goto v___jp_318_;
}
else
{
lean_object* v___x_343_; 
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
lean_inc(v___y_314_);
lean_inc_ref(v___y_313_);
lean_inc_ref(v_x_310_);
v___x_343_ = lean_infer_type(v_x_310_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; uint8_t v___x_345_; lean_object* v___x_346_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc(v_a_344_);
lean_dec_ref_known(v___x_343_, 1);
v___x_345_ = 0;
v___x_346_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_a_344_, v___f_339_, v___x_345_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = lean_array_get_size(v_x_311_);
v___x_349_ = lean_nat_dec_le(v_a_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec(v_a_347_);
lean_dec_ref_known(v_x_310_, 2);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_k_309_);
v___y_319_ = v___y_313_;
v___y_320_ = v___y_314_;
v___y_321_ = v___y_315_;
v___y_322_ = v___y_316_;
goto v___jp_318_;
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___f_355_; lean_object* v___x_356_; 
lean_dec_ref(v_e_308_);
v___x_350_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_347_);
lean_inc_ref(v_x_311_);
v___x_351_ = l_Array_toSubarray___redArg(v_x_311_, v___x_350_, v_a_347_);
v___x_352_ = l_Subarray_copy___redArg(v___x_351_);
v___x_353_ = l_Lean_mkAppN(v_x_310_, v___x_352_);
lean_dec_ref(v___x_352_);
v___x_354_ = l_Array_toSubarray___redArg(v_x_311_, v_a_347_, v___x_348_);
lean_inc_ref(v___x_353_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_355_, 0, v___x_354_);
lean_closure_set(v___f_355_, 1, v_k_309_);
lean_closure_set(v___f_355_, 2, v___x_353_);
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
lean_inc(v___y_314_);
lean_inc_ref(v___y_313_);
v___x_356_ = lean_infer_type(v___x_353_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v___x_358_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4));
v___x_359_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v___x_358_, v_a_357_, v___f_355_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
return v___x_359_;
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec_ref(v___f_355_);
v_a_360_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_356_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_356_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref_known(v_x_310_, 2);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_k_309_);
lean_dec_ref(v_e_308_);
v_a_368_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_346_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_346_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref_known(v_x_310_, 2);
lean_dec_ref(v_x_311_);
lean_dec_ref(v_k_309_);
lean_dec_ref(v_e_308_);
v_a_376_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_343_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_343_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_311_);
lean_dec_ref(v_x_310_);
lean_dec_ref(v_k_309_);
v___y_319_ = v___y_313_;
v___y_320_ = v___y_314_;
v___y_321_ = v___y_315_;
v___y_322_ = v___y_316_;
goto v___jp_318_;
}
}
}
v___jp_318_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1);
v___x_324_ = l_Lean_indentExpr(v_e_308_);
v___x_325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_325_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
return v___x_326_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_308_ = stack[0].m_obj;
lean_object* v_k_309_ = stack[1].m_obj;
lean_object* v_x_310_ = stack[2].m_obj;
lean_object* v_x_311_ = stack[3].m_obj;
lean_object* v_x_312_ = stack[4].m_obj;
lean_object* v___y_313_ = stack[5].m_obj;
lean_object* v___y_314_ = stack[6].m_obj;
lean_object* v___y_315_ = stack[7].m_obj;
lean_object* v___y_316_ = stack[8].m_obj;
lean_object* v_res_384_;
v_res_384_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_308_, v_k_309_, v_x_310_, v_x_311_, v_x_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
stack->m_obj
 = v_res_384_;
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(lean_object* v_e_385_, lean_object* v_k_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_dummy_392_; lean_object* v_nargs_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_dummy_392_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_393_ = l_Lean_Expr_getAppNumArgs(v_e_385_);
lean_inc(v_nargs_393_);
v___x_394_ = lean_mk_array(v_nargs_393_, v_dummy_392_);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_sub(v_nargs_393_, v___x_395_);
lean_dec(v_nargs_393_);
lean_inc_ref(v_e_385_);
v___x_397_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_385_, v_k_386_, v_e_385_, v___x_394_, v___x_396_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
return v___x_397_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_385_ = stack[0].m_obj;
lean_object* v_k_386_ = stack[1].m_obj;
lean_object* v_a_387_ = stack[2].m_obj;
lean_object* v_a_388_ = stack[3].m_obj;
lean_object* v_a_389_ = stack[4].m_obj;
lean_object* v_a_390_ = stack[5].m_obj;
lean_object* v_res_398_;
v_res_398_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_385_, v_k_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
stack->m_obj
 = v_res_398_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___boxed(lean_object* v_e_399_, lean_object* v_k_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_399_, v_k_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object* v_e_407_, lean_object* v_k_408_, lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_407_, v_k_408_, v_x_409_, v_x_410_, v_x_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_417_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_object* v_00_u03b1_418_, lean_object* v_e_419_, lean_object* v_k_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_419_, v_k_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
return v___x_426_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_419_ = stack[1].m_obj;
lean_object* v_k_420_ = stack[2].m_obj;
lean_object* v_a_421_ = stack[3].m_obj;
lean_object* v_a_422_ = stack[4].m_obj;
lean_object* v_a_423_ = stack[5].m_obj;
lean_object* v_a_424_ = stack[6].m_obj;
lean_object* v_res_427_;
v_res_427_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_box(0), v_e_419_, v_k_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
stack->m_obj
 = v_res_427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___boxed(lean_object* v_00_u03b1_428_, lean_object* v_e_429_, lean_object* v_k_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(v_00_u03b1_428_, v_e_429_, v_k_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_436_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_object* v_00_u03b1_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_438_ = stack[1].m_obj;
lean_object* v___y_439_ = stack[2].m_obj;
lean_object* v___y_440_ = stack[3].m_obj;
lean_object* v___y_441_ = stack[4].m_obj;
lean_object* v___y_442_ = stack[5].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_box(0), v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___boxed(lean_object* v_00_u03b1_446_, lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(v_00_u03b1_446_, v_msg_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
return v_res_453_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_object* v_00_u03b1_454_, lean_object* v_name_455_, uint8_t v_bi_456_, lean_object* v_type_457_, lean_object* v_k_458_, uint8_t v_kind_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_455_, v_bi_456_, v_type_457_, v_k_458_, v_kind_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
return v___x_465_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_455_ = stack[1].m_obj;
uint8_t v_bi_456_ = stack[2].m_num;
lean_object* v_type_457_ = stack[3].m_obj;
lean_object* v_k_458_ = stack[4].m_obj;
uint8_t v_kind_459_ = stack[5].m_num;
lean_object* v___y_460_ = stack[6].m_obj;
lean_object* v___y_461_ = stack[7].m_obj;
lean_object* v___y_462_ = stack[8].m_obj;
lean_object* v___y_463_ = stack[9].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_box(0), v_name_455_, v_bi_456_, v_type_457_, v_k_458_, v_kind_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_467_, lean_object* v_name_468_, lean_object* v_bi_469_, lean_object* v_type_470_, lean_object* v_k_471_, lean_object* v_kind_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
uint8_t v_bi_boxed_478_; uint8_t v_kind_boxed_479_; lean_object* v_res_480_; 
v_bi_boxed_478_ = lean_unbox(v_bi_469_);
v_kind_boxed_479_ = lean_unbox(v_kind_472_);
v_res_480_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(v_00_u03b1_467_, v_name_468_, v_bi_boxed_478_, v_type_470_, v_k_471_, v_kind_boxed_479_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_480_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_object* v_00_u03b1_481_, lean_object* v_name_482_, lean_object* v_type_483_, lean_object* v_k_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v_name_482_, v_type_483_, v_k_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
return v___x_490_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_482_ = stack[1].m_obj;
lean_object* v_type_483_ = stack[2].m_obj;
lean_object* v_k_484_ = stack[3].m_obj;
lean_object* v___y_485_ = stack[4].m_obj;
lean_object* v___y_486_ = stack[5].m_obj;
lean_object* v___y_487_ = stack[6].m_obj;
lean_object* v___y_488_ = stack[7].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_box(0), v_name_482_, v_type_483_, v_k_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___boxed(lean_object* v_00_u03b1_492_, lean_object* v_name_493_, lean_object* v_type_494_, lean_object* v_k_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(v_00_u03b1_492_, v_name_493_, v_type_494_, v_k_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_object* v_00_u03b1_502_, lean_object* v_e_503_, lean_object* v_k_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_503_, v_k_504_, v_x_505_, v_x_506_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
return v___x_513_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_503_ = stack[1].m_obj;
lean_object* v_k_504_ = stack[2].m_obj;
lean_object* v_x_505_ = stack[3].m_obj;
lean_object* v_x_506_ = stack[4].m_obj;
lean_object* v_x_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v___y_509_ = stack[7].m_obj;
lean_object* v___y_510_ = stack[8].m_obj;
lean_object* v___y_511_ = stack[9].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_box(0), v_e_503_, v_k_504_, v_x_505_, v_x_506_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___boxed(lean_object* v_00_u03b1_515_, lean_object* v_e_516_, lean_object* v_k_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(v_00_u03b1_515_, v_e_516_, v_k_517_, v_x_518_, v_x_519_, v_x_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_526_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object* v___x_527_, uint8_t v___x_528_, lean_object* v_brecOnApp_529_, lean_object* v_x_530_, lean_object* v_c_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_mkEq(v_c_531_, v___x_527_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; uint8_t v___x_543_; lean_object* v___x_544_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = lean_unsigned_to_nat(1u);
v___x_540_ = lean_mk_empty_array_with_capacity(v___x_539_);
v___x_541_ = lean_array_push(v___x_540_, v_x_530_);
v___x_542_ = 0;
v___x_543_ = 1;
v___x_544_ = l_Lean_Meta_mkLambdaFVars(v___x_541_, v_a_538_, v___x_542_, v___x_528_, v___x_542_, v___x_528_, v___x_543_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
lean_dec_ref(v___x_541_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_553_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_brecOnApp_529_);
lean_ctor_set(v___x_549_, 1, v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v_brecOnApp_529_);
v_a_554_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_544_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_544_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec_ref(v_x_530_);
lean_dec_ref(v_brecOnApp_529_);
v_a_562_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_537_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_537_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_527_ = stack[0].m_obj;
uint8_t v___x_528_ = stack[1].m_num;
lean_object* v_brecOnApp_529_ = stack[2].m_obj;
lean_object* v_x_530_ = stack[3].m_obj;
lean_object* v_c_531_ = stack[4].m_obj;
lean_object* v___y_532_ = stack[5].m_obj;
lean_object* v___y_533_ = stack[6].m_obj;
lean_object* v___y_534_ = stack[7].m_obj;
lean_object* v___y_535_ = stack[8].m_obj;
lean_object* v_res_570_;
v_res_570_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(v___x_527_, v___x_528_, v_brecOnApp_529_, v_x_530_, v_c_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed(lean_object* v___x_571_, lean_object* v___x_572_, lean_object* v_brecOnApp_573_, lean_object* v_x_574_, lean_object* v_c_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
uint8_t v___x_553__boxed_581_; lean_object* v_res_582_; 
v___x_553__boxed_581_ = lean_unbox(v___x_572_);
v_res_582_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(v___x_571_, v___x_553__boxed_581_, v_brecOnApp_573_, v_x_574_, v_c_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_582_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2));
v___x_588_ = l_Lean_stringToMessageData(v___x_587_);
return v___x_588_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(lean_object* v_goal_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_596_ = lean_unsigned_to_nat(3u);
v___x_597_ = l_Lean_Expr_isAppOfArity(v_goal_589_, v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3);
v___x_599_ = l_Lean_indentExpr(v_goal_589_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_600_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___f_606_; lean_object* v___x_607_; 
v___x_602_ = l_Lean_Expr_appFn_x21(v_goal_589_);
v___x_603_ = l_Lean_Expr_appArg_x21(v___x_602_);
lean_dec_ref(v___x_602_);
v___x_604_ = l_Lean_Expr_appArg_x21(v_goal_589_);
lean_dec_ref(v_goal_589_);
v___x_605_ = lean_box(v___x_597_);
v___f_606_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed), 10, 2);
lean_closure_set(v___f_606_, 0, v___x_604_);
lean_closure_set(v___f_606_, 1, v___x_605_);
v___x_607_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v___x_603_, v___f_606_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v___x_607_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_589_ = stack[0].m_obj;
lean_object* v_a_590_ = stack[1].m_obj;
lean_object* v_a_591_ = stack[2].m_obj;
lean_object* v_a_592_ = stack[3].m_obj;
lean_object* v_a_593_ = stack[4].m_obj;
lean_object* v_res_608_;
v_res_608_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_goal_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___boxed(lean_object* v_goal_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_goal_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
return v_res_615_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(lean_object* v_mvarId_616_, lean_object* v_x_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_a_632_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_623_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_623_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_616_ = stack[0].m_obj;
lean_object* v_x_617_ = stack[1].m_obj;
lean_object* v___y_618_ = stack[2].m_obj;
lean_object* v___y_619_ = stack[3].m_obj;
lean_object* v___y_620_ = stack[4].m_obj;
lean_object* v___y_621_ = stack[5].m_obj;
lean_object* v_res_640_;
v_res_640_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_);
stack->m_obj
 = v_res_640_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_641_, lean_object* v_x_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_641_, v_x_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
return v_res_648_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_object* v_00_u03b1_649_, lean_object* v_mvarId_650_, lean_object* v_x_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_650_, v_x_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
return v___x_657_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_650_ = stack[1].m_obj;
lean_object* v_x_651_ = stack[2].m_obj;
lean_object* v___y_652_ = stack[3].m_obj;
lean_object* v___y_653_ = stack[4].m_obj;
lean_object* v___y_654_ = stack[5].m_obj;
lean_object* v___y_655_ = stack[6].m_obj;
lean_object* v_res_658_;
v_res_658_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_box(0), v_mvarId_650_, v_x_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___boxed(lean_object* v_00_u03b1_659_, lean_object* v_mvarId_660_, lean_object* v_x_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(v_00_u03b1_659_, v_mvarId_660_, v_x_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_667_;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(lean_object* v_declName_668_, lean_object* v_x_669_){
_start:
{
uint8_t v___x_670_; 
v___x_670_ = lean_name_eq(v_x_669_, v_declName_668_);
return v___x_670_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_668_ = stack[0].m_obj;
lean_object* v_x_669_ = stack[1].m_obj;
uint8_t v_res_671_;
v_res_671_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(v_declName_668_, v_x_669_);
stack->m_num = v_res_671_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed(lean_object* v_declName_672_, lean_object* v_x_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(v_declName_672_, v_x_673_);
lean_dec(v_x_673_);
lean_dec(v_declName_672_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(lean_object* v_mvarId_676_, lean_object* v___f_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
lean_inc(v_mvarId_676_);
v___x_683_ = l_Lean_MVarId_getType_x27(v_mvarId_676_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_753_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_753_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_753_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_753_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_689_ = lean_unsigned_to_nat(3u);
v___x_690_ = l_Lean_Expr_isAppOfArity(v_a_684_, v___x_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_693_; 
lean_dec(v_a_684_);
lean_dec_ref(v___f_677_);
lean_dec(v_mvarId_676_);
v___x_691_ = lean_box(0);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_691_);
v___x_693_ = v___x_686_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; lean_object* v___x_700_; 
lean_del_object(v___x_686_);
v___x_695_ = l_Lean_Expr_appFn_x21(v_a_684_);
v___x_696_ = l_Lean_Expr_appArg_x21(v___x_695_);
lean_dec_ref(v___x_695_);
v___x_697_ = l_Lean_Expr_appArg_x21(v_a_684_);
lean_dec(v_a_684_);
v___x_698_ = l_Lean_Expr_consumeMData(v___x_697_);
lean_dec_ref(v___x_697_);
v___x_699_ = 0;
v___x_700_ = l_Lean_Meta_delta_x3f(v___x_698_, v___f_677_, v___x_699_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_744_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_744_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_744_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_744_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
if (lean_obj_tag(v_a_701_) == 1)
{
lean_object* v_val_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_703_);
v_val_705_ = lean_ctor_get(v_a_701_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v_a_701_);
if (v_isSharedCheck_739_ == 0)
{
v___x_707_ = v_a_701_;
v_isShared_708_ = v_isSharedCheck_739_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_val_705_);
lean_dec(v_a_701_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_739_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_mkEq(v___x_696_, v_val_705_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_676_, v_a_710_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_722_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v_a_712_);
v___x_717_ = v___x_707_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_717_);
v___x_719_ = v___x_714_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_del_object(v___x_707_);
v_a_723_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_711_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_711_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_del_object(v___x_707_);
lean_dec(v_mvarId_676_);
v_a_731_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_709_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_709_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec(v_a_701_);
lean_dec_ref(v___x_696_);
lean_dec(v_mvarId_676_);
v___x_740_ = lean_box(0);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_740_);
v___x_742_ = v___x_703_;
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
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v___x_696_);
lean_dec(v_mvarId_676_);
v_a_745_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_700_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_700_);
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
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___f_677_);
lean_dec(v_mvarId_676_);
v_a_754_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_683_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_683_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_676_ = stack[0].m_obj;
lean_object* v___f_677_ = stack[1].m_obj;
lean_object* v___y_678_ = stack[2].m_obj;
lean_object* v___y_679_ = stack[3].m_obj;
lean_object* v___y_680_ = stack[4].m_obj;
lean_object* v___y_681_ = stack[5].m_obj;
lean_object* v_res_762_;
v_res_762_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(v_mvarId_676_, v___f_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
stack->m_obj
 = v_res_762_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object* v_mvarId_763_, lean_object* v___f_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(v_mvarId_763_, v___f_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_770_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object* v_mvarId_771_, lean_object* v_declName_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___f_778_; lean_object* v___f_779_; lean_object* v___x_780_; 
v___f_778_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_778_, 0, v_declName_772_);
lean_inc(v_mvarId_771_);
v___f_779_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_779_, 0, v_mvarId_771_);
lean_closure_set(v___f_779_, 1, v___f_778_);
v___x_780_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_771_, v___f_779_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_780_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_771_ = stack[0].m_obj;
lean_object* v_declName_772_ = stack[1].m_obj;
lean_object* v_a_773_ = stack[2].m_obj;
lean_object* v_a_774_ = stack[3].m_obj;
lean_object* v_a_775_ = stack[4].m_obj;
lean_object* v_a_776_ = stack[5].m_obj;
lean_object* v_res_781_;
v_res_781_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_771_, v_declName_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object* v_mvarId_782_, lean_object* v_declName_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_782_, v_declName_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
return v_res_789_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_790_ = lean_unsigned_to_nat(32u);
v___x_791_ = lean_mk_empty_array_with_capacity(v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_793_ = ((size_t)5ULL);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_unsigned_to_nat(32u);
v___x_796_ = lean_mk_empty_array_with_capacity(v___x_795_);
v___x_797_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0);
v___x_798_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
lean_ctor_set(v___x_798_, 2, v___x_794_);
lean_ctor_set(v___x_798_, 3, v___x_794_);
lean_ctor_set_usize(v___x_798_, 4, v___x_793_);
return v___x_798_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v_traceState_802_; lean_object* v_traces_803_; lean_object* v___x_804_; lean_object* v_traceState_805_; lean_object* v_env_806_; lean_object* v_nextMacroScope_807_; lean_object* v_ngen_808_; lean_object* v_auxDeclNGen_809_; lean_object* v_cache_810_; lean_object* v_recordedDeps_811_; lean_object* v_messages_812_; lean_object* v_infoState_813_; lean_object* v_snapshotTasks_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_833_; 
v___x_801_ = lean_st_ref_get(v___y_799_);
v_traceState_802_ = lean_ctor_get(v___x_801_, 4);
lean_inc_ref(v_traceState_802_);
lean_dec(v___x_801_);
v_traces_803_ = lean_ctor_get(v_traceState_802_, 0);
lean_inc_ref(v_traces_803_);
lean_dec_ref(v_traceState_802_);
v___x_804_ = lean_st_ref_take(v___y_799_);
v_traceState_805_ = lean_ctor_get(v___x_804_, 4);
v_env_806_ = lean_ctor_get(v___x_804_, 0);
v_nextMacroScope_807_ = lean_ctor_get(v___x_804_, 1);
v_ngen_808_ = lean_ctor_get(v___x_804_, 2);
v_auxDeclNGen_809_ = lean_ctor_get(v___x_804_, 3);
v_cache_810_ = lean_ctor_get(v___x_804_, 5);
v_recordedDeps_811_ = lean_ctor_get(v___x_804_, 6);
v_messages_812_ = lean_ctor_get(v___x_804_, 7);
v_infoState_813_ = lean_ctor_get(v___x_804_, 8);
v_snapshotTasks_814_ = lean_ctor_get(v___x_804_, 9);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_833_ == 0)
{
v___x_816_ = v___x_804_;
v_isShared_817_ = v_isSharedCheck_833_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_snapshotTasks_814_);
lean_inc(v_infoState_813_);
lean_inc(v_messages_812_);
lean_inc(v_recordedDeps_811_);
lean_inc(v_cache_810_);
lean_inc(v_traceState_805_);
lean_inc(v_auxDeclNGen_809_);
lean_inc(v_ngen_808_);
lean_inc(v_nextMacroScope_807_);
lean_inc(v_env_806_);
lean_dec(v___x_804_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_833_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint64_t v_tid_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_831_; 
v_tid_818_ = lean_ctor_get_uint64(v_traceState_805_, sizeof(void*)*1);
v_isSharedCheck_831_ = !lean_is_exclusive(v_traceState_805_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v_traceState_805_, 0);
lean_dec(v_unused_832_);
v___x_820_ = v_traceState_805_;
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
else
{
lean_dec(v_traceState_805_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_822_);
lean_ctor_set_uint64(v_reuseFailAlloc_830_, sizeof(void*)*1, v_tid_818_);
v___x_824_ = v_reuseFailAlloc_830_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_826_; 
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 4, v___x_824_);
v___x_826_ = v___x_816_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_env_806_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_nextMacroScope_807_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_ngen_808_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_auxDeclNGen_809_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_829_, 5, v_cache_810_);
lean_ctor_set(v_reuseFailAlloc_829_, 6, v_recordedDeps_811_);
lean_ctor_set(v_reuseFailAlloc_829_, 7, v_messages_812_);
lean_ctor_set(v_reuseFailAlloc_829_, 8, v_infoState_813_);
lean_ctor_set(v_reuseFailAlloc_829_, 9, v_snapshotTasks_814_);
v___x_826_ = v_reuseFailAlloc_829_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_st_ref_put(v___y_799_, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v_traces_803_);
return v___x_828_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_799_ = stack[0].m_obj;
lean_object* v_res_834_;
v_res_834_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_799_);
stack->m_obj
 = v_res_834_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___boxed(lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_835_);
lean_dec(v___y_835_);
return v_res_837_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_841_);
return v___x_843_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_838_ = stack[0].m_obj;
lean_object* v___y_839_ = stack[1].m_obj;
lean_object* v___y_840_ = stack[2].m_obj;
lean_object* v___y_841_ = stack[3].m_obj;
lean_object* v_res_844_;
v_res_844_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v___y_838_, v___y_839_, v___y_840_, v___y_841_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_850_;
}
}
uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v_opts_851_, lean_object* v_opt_852_){
_start:
{
lean_object* v_name_853_; lean_object* v_defValue_854_; lean_object* v_map_855_; lean_object* v___x_856_; 
v_name_853_ = lean_ctor_get(v_opt_852_, 0);
v_defValue_854_ = lean_ctor_get(v_opt_852_, 1);
v_map_855_ = lean_ctor_get(v_opts_851_, 0);
v___x_856_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_855_, v_name_853_);
if (lean_obj_tag(v___x_856_) == 0)
{
uint8_t v___x_857_; 
v___x_857_ = lean_unbox(v_defValue_854_);
return v___x_857_;
}
else
{
lean_object* v_val_858_; 
v_val_858_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___x_856_, 1);
if (lean_obj_tag(v_val_858_) == 1)
{
uint8_t v_v_859_; 
v_v_859_ = lean_ctor_get_uint8(v_val_858_, 0);
lean_dec_ref_known(v_val_858_, 0);
return v_v_859_;
}
else
{
uint8_t v___x_860_; 
lean_dec(v_val_858_);
v___x_860_ = lean_unbox(v_defValue_854_);
return v___x_860_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_851_ = stack[0].m_obj;
lean_object* v_opt_852_ = stack[1].m_obj;
uint8_t v_res_861_;
v_res_861_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_851_, v_opt_852_);
stack->m_num = v_res_861_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v_opts_862_, lean_object* v_opt_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_862_, v_opt_863_);
lean_dec_ref(v_opt_863_);
lean_dec_ref(v_opts_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* v_mvarId_869_, lean_object* v_x_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_876_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
v___x_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_877_, 0, v_mvarId_869_);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_869_ = stack[0].m_obj;
lean_object* v_x_870_ = stack[1].m_obj;
lean_object* v___y_871_ = stack[2].m_obj;
lean_object* v___y_872_ = stack[3].m_obj;
lean_object* v___y_873_ = stack[4].m_obj;
lean_object* v___y_874_ = stack[5].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(v_mvarId_869_, v_x_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object* v_mvarId_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(v_mvarId_881_, v_x_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec_ref(v_x_882_);
return v_res_888_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* v_____r_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_box(0);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_____r_889_ = stack[0].m_obj;
lean_object* v___y_890_ = stack[1].m_obj;
lean_object* v___y_891_ = stack[2].m_obj;
lean_object* v___y_892_ = stack[3].m_obj;
lean_object* v___y_893_ = stack[4].m_obj;
lean_object* v_res_897_;
v_res_897_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_____r_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object* v_____r_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_____r_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
return v_res_904_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_905_; double v___x_906_; 
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_float_of_nat(v___x_905_);
return v___x_906_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v_cls_910_, lean_object* v_msg_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_ref_917_; lean_object* v___x_918_; lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_964_; 
v_ref_917_ = lean_ctor_get(v___y_914_, 2);
v___x_918_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_964_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_964_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_964_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v_traceState_924_; lean_object* v_env_925_; lean_object* v_nextMacroScope_926_; lean_object* v_ngen_927_; lean_object* v_auxDeclNGen_928_; lean_object* v_cache_929_; lean_object* v_recordedDeps_930_; lean_object* v_messages_931_; lean_object* v_infoState_932_; lean_object* v_snapshotTasks_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_963_; 
v___x_923_ = lean_st_ref_take(v___y_915_);
v_traceState_924_ = lean_ctor_get(v___x_923_, 4);
v_env_925_ = lean_ctor_get(v___x_923_, 0);
v_nextMacroScope_926_ = lean_ctor_get(v___x_923_, 1);
v_ngen_927_ = lean_ctor_get(v___x_923_, 2);
v_auxDeclNGen_928_ = lean_ctor_get(v___x_923_, 3);
v_cache_929_ = lean_ctor_get(v___x_923_, 5);
v_recordedDeps_930_ = lean_ctor_get(v___x_923_, 6);
v_messages_931_ = lean_ctor_get(v___x_923_, 7);
v_infoState_932_ = lean_ctor_get(v___x_923_, 8);
v_snapshotTasks_933_ = lean_ctor_get(v___x_923_, 9);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_963_ == 0)
{
v___x_935_ = v___x_923_;
v_isShared_936_ = v_isSharedCheck_963_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_snapshotTasks_933_);
lean_inc(v_infoState_932_);
lean_inc(v_messages_931_);
lean_inc(v_recordedDeps_930_);
lean_inc(v_cache_929_);
lean_inc(v_traceState_924_);
lean_inc(v_auxDeclNGen_928_);
lean_inc(v_ngen_927_);
lean_inc(v_nextMacroScope_926_);
lean_inc(v_env_925_);
lean_dec(v___x_923_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_963_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
uint64_t v_tid_937_; lean_object* v_traces_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_962_; 
v_tid_937_ = lean_ctor_get_uint64(v_traceState_924_, sizeof(void*)*1);
v_traces_938_ = lean_ctor_get(v_traceState_924_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v_traceState_924_);
if (v_isSharedCheck_962_ == 0)
{
v___x_940_ = v_traceState_924_;
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_traces_938_);
lean_dec(v_traceState_924_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_962_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; double v___x_944_; uint8_t v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_942_ = lean_box(0);
v___x_943_ = lean_box(0);
v___x_944_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
v___x_945_ = 0;
v___x_946_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_947_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_947_, 0, v_cls_910_);
lean_ctor_set(v___x_947_, 1, v___x_943_);
lean_ctor_set(v___x_947_, 2, v___x_946_);
lean_ctor_set_float(v___x_947_, sizeof(void*)*3, v___x_944_);
lean_ctor_set_float(v___x_947_, sizeof(void*)*3 + 8, v___x_944_);
lean_ctor_set_uint8(v___x_947_, sizeof(void*)*3 + 16, v___x_945_);
v___x_948_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2));
v___x_949_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v_a_919_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
lean_inc(v_ref_917_);
v___x_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_950_, 0, v_ref_917_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Lean_PersistentArray_push___redArg(v_traces_938_, v___x_950_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_951_);
v___x_953_ = v___x_940_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_951_);
lean_ctor_set_uint64(v_reuseFailAlloc_961_, sizeof(void*)*1, v_tid_937_);
v___x_953_ = v_reuseFailAlloc_961_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 4, v___x_953_);
v___x_955_ = v___x_935_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_env_925_);
lean_ctor_set(v_reuseFailAlloc_960_, 1, v_nextMacroScope_926_);
lean_ctor_set(v_reuseFailAlloc_960_, 2, v_ngen_927_);
lean_ctor_set(v_reuseFailAlloc_960_, 3, v_auxDeclNGen_928_);
lean_ctor_set(v_reuseFailAlloc_960_, 4, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_960_, 5, v_cache_929_);
lean_ctor_set(v_reuseFailAlloc_960_, 6, v_recordedDeps_930_);
lean_ctor_set(v_reuseFailAlloc_960_, 7, v_messages_931_);
lean_ctor_set(v_reuseFailAlloc_960_, 8, v_infoState_932_);
lean_ctor_set(v_reuseFailAlloc_960_, 9, v_snapshotTasks_933_);
v___x_955_ = v_reuseFailAlloc_960_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = lean_st_ref_put(v___y_915_, v___x_955_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_942_);
v___x_958_ = v___x_921_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_942_);
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
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_910_ = stack[0].m_obj;
lean_object* v_msg_911_ = stack[1].m_obj;
lean_object* v___y_912_ = stack[2].m_obj;
lean_object* v___y_913_ = stack[3].m_obj;
lean_object* v___y_914_ = stack[4].m_obj;
lean_object* v___y_915_ = stack[5].m_obj;
lean_object* v_res_965_;
v_res_965_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_910_, v_msg_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
stack->m_obj
 = v_res_965_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_966_, v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(lean_object* v_opts_974_, lean_object* v_opt_975_){
_start:
{
lean_object* v_name_976_; lean_object* v_defValue_977_; lean_object* v_map_978_; lean_object* v___x_979_; 
v_name_976_ = lean_ctor_get(v_opt_975_, 0);
v_defValue_977_ = lean_ctor_get(v_opt_975_, 1);
v_map_978_ = lean_ctor_get(v_opts_974_, 0);
v___x_979_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_978_, v_name_976_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_inc(v_defValue_977_);
return v_defValue_977_;
}
else
{
lean_object* v_val_980_; 
v_val_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v___x_979_, 1);
if (lean_obj_tag(v_val_980_) == 3)
{
lean_object* v_v_981_; 
v_v_981_ = lean_ctor_get(v_val_980_, 0);
lean_inc(v_v_981_);
lean_dec_ref_known(v_val_980_, 1);
return v_v_981_;
}
else
{
lean_dec(v_val_980_);
lean_inc(v_defValue_977_);
return v_defValue_977_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8___boxed(lean_object* v_opts_982_, lean_object* v_opt_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_982_, v_opt_983_);
lean_dec_ref(v_opt_983_);
lean_dec_ref(v_opts_982_);
return v_res_984_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(size_t v_sz_985_, size_t v_i_986_, lean_object* v_bs_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = lean_usize_dec_lt(v_i_986_, v_sz_985_);
if (v___x_988_ == 0)
{
return v_bs_987_;
}
else
{
lean_object* v_v_989_; lean_object* v_msg_990_; lean_object* v___x_991_; lean_object* v_bs_x27_992_; size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
v_v_989_ = lean_array_uget_borrowed(v_bs_987_, v_i_986_);
v_msg_990_ = lean_ctor_get(v_v_989_, 1);
lean_inc_ref(v_msg_990_);
v___x_991_ = lean_unsigned_to_nat(0u);
v_bs_x27_992_ = lean_array_uset(v_bs_987_, v_i_986_, v___x_991_);
v___x_993_ = ((size_t)1ULL);
v___x_994_ = lean_usize_add(v_i_986_, v___x_993_);
v___x_995_ = lean_array_uset(v_bs_x27_992_, v_i_986_, v_msg_990_);
v_i_986_ = v___x_994_;
v_bs_987_ = v___x_995_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_985_ = stack[0].m_num;
size_t v_i_986_ = stack[1].m_num;
lean_object* v_bs_987_ = stack[2].m_obj;
lean_object* v_res_997_;
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_985_, v_i_986_, v_bs_987_);
stack->m_obj
 = v_res_997_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_998_, lean_object* v_i_999_, lean_object* v_bs_1000_){
_start:
{
size_t v_sz_boxed_1001_; size_t v_i_boxed_1002_; lean_object* v_res_1003_; 
v_sz_boxed_1001_ = lean_unbox_usize(v_sz_998_);
lean_dec(v_sz_998_);
v_i_boxed_1002_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_boxed_1001_, v_i_boxed_1002_, v_bs_1000_);
return v_res_1003_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object* v_oldTraces_1004_, lean_object* v_data_1005_, lean_object* v_ref_1006_, lean_object* v_msg_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_toCold_1013_; lean_object* v_currRecDepth_1014_; lean_object* v_ref_1015_; uint16_t v_optionFlags_1016_; uint8_t v_suppressElabErrors_1017_; uint8_t v_isRecordingDeps_1018_; lean_object* v_ref_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v_traceState_1022_; lean_object* v_traces_1023_; lean_object* v___x_1024_; size_t v_sz_1025_; size_t v___x_1026_; lean_object* v___x_1027_; lean_object* v_msg_1028_; lean_object* v___x_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1068_; 
v_toCold_1013_ = lean_ctor_get(v___y_1010_, 0);
v_currRecDepth_1014_ = lean_ctor_get(v___y_1010_, 1);
v_ref_1015_ = lean_ctor_get(v___y_1010_, 2);
v_optionFlags_1016_ = lean_ctor_get_uint16(v___y_1010_, sizeof(void*)*3);
v_suppressElabErrors_1017_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1018_ = lean_ctor_get_uint8(v___y_1010_, sizeof(void*)*3 + 3);
v_ref_1019_ = l_Lean_replaceRef(v_ref_1006_, v_ref_1015_);
lean_inc(v_currRecDepth_1014_);
lean_inc_ref(v_toCold_1013_);
v___x_1020_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1020_, 0, v_toCold_1013_);
lean_ctor_set(v___x_1020_, 1, v_currRecDepth_1014_);
lean_ctor_set(v___x_1020_, 2, v_ref_1019_);
lean_ctor_set_uint16(v___x_1020_, sizeof(void*)*3, v_optionFlags_1016_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*3 + 2, v_suppressElabErrors_1017_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*3 + 3, v_isRecordingDeps_1018_);
v___x_1021_ = lean_st_ref_get(v___y_1011_);
v_traceState_1022_ = lean_ctor_get(v___x_1021_, 4);
lean_inc_ref(v_traceState_1022_);
lean_dec(v___x_1021_);
v_traces_1023_ = lean_ctor_get(v_traceState_1022_, 0);
lean_inc_ref(v_traces_1023_);
lean_dec_ref(v_traceState_1022_);
v___x_1024_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1023_);
lean_dec_ref(v_traces_1023_);
v_sz_1025_ = lean_array_size(v___x_1024_);
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_1025_, v___x_1026_, v___x_1024_);
v_msg_1028_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1028_, 0, v_data_1005_);
lean_ctor_set(v_msg_1028_, 1, v_msg_1007_);
lean_ctor_set(v_msg_1028_, 2, v___x_1027_);
v___x_1029_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_1028_, v___y_1008_, v___y_1009_, v___x_1020_, v___y_1011_);
lean_dec_ref_known(v___x_1020_, 3);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1068_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1068_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v_traceState_1035_; lean_object* v_env_1036_; lean_object* v_nextMacroScope_1037_; lean_object* v_ngen_1038_; lean_object* v_auxDeclNGen_1039_; lean_object* v_cache_1040_; lean_object* v_recordedDeps_1041_; lean_object* v_messages_1042_; lean_object* v_infoState_1043_; lean_object* v_snapshotTasks_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1067_; 
v___x_1034_ = lean_st_ref_take(v___y_1011_);
v_traceState_1035_ = lean_ctor_get(v___x_1034_, 4);
v_env_1036_ = lean_ctor_get(v___x_1034_, 0);
v_nextMacroScope_1037_ = lean_ctor_get(v___x_1034_, 1);
v_ngen_1038_ = lean_ctor_get(v___x_1034_, 2);
v_auxDeclNGen_1039_ = lean_ctor_get(v___x_1034_, 3);
v_cache_1040_ = lean_ctor_get(v___x_1034_, 5);
v_recordedDeps_1041_ = lean_ctor_get(v___x_1034_, 6);
v_messages_1042_ = lean_ctor_get(v___x_1034_, 7);
v_infoState_1043_ = lean_ctor_get(v___x_1034_, 8);
v_snapshotTasks_1044_ = lean_ctor_get(v___x_1034_, 9);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1046_ = v___x_1034_;
v_isShared_1047_ = v_isSharedCheck_1067_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_snapshotTasks_1044_);
lean_inc(v_infoState_1043_);
lean_inc(v_messages_1042_);
lean_inc(v_recordedDeps_1041_);
lean_inc(v_cache_1040_);
lean_inc(v_traceState_1035_);
lean_inc(v_auxDeclNGen_1039_);
lean_inc(v_ngen_1038_);
lean_inc(v_nextMacroScope_1037_);
lean_inc(v_env_1036_);
lean_dec(v___x_1034_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1067_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
uint64_t v_tid_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1065_; 
v_tid_1048_ = lean_ctor_get_uint64(v_traceState_1035_, sizeof(void*)*1);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_traceState_1035_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v_traceState_1035_, 0);
lean_dec(v_unused_1066_);
v___x_1050_ = v_traceState_1035_;
v_isShared_1051_ = v_isSharedCheck_1065_;
goto v_resetjp_1049_;
}
else
{
lean_dec(v_traceState_1035_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1065_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_ref_1006_);
lean_ctor_set(v___x_1053_, 1, v_a_1030_);
v___x_1054_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1004_, v___x_1053_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1054_);
v___x_1056_ = v___x_1050_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1054_);
lean_ctor_set_uint64(v_reuseFailAlloc_1064_, sizeof(void*)*1, v_tid_1048_);
v___x_1056_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1058_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 4, v___x_1056_);
v___x_1058_ = v___x_1046_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_env_1036_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_nextMacroScope_1037_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_ngen_1038_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_auxDeclNGen_1039_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1063_, 5, v_cache_1040_);
lean_ctor_set(v_reuseFailAlloc_1063_, 6, v_recordedDeps_1041_);
lean_ctor_set(v_reuseFailAlloc_1063_, 7, v_messages_1042_);
lean_ctor_set(v_reuseFailAlloc_1063_, 8, v_infoState_1043_);
lean_ctor_set(v_reuseFailAlloc_1063_, 9, v_snapshotTasks_1044_);
v___x_1058_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = lean_st_ref_put(v___y_1011_, v___x_1058_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1052_);
v___x_1061_ = v___x_1032_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1052_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1004_ = stack[0].m_obj;
lean_object* v_data_1005_ = stack[1].m_obj;
lean_object* v_ref_1006_ = stack[2].m_obj;
lean_object* v_msg_1007_ = stack[3].m_obj;
lean_object* v___y_1008_ = stack[4].m_obj;
lean_object* v___y_1009_ = stack[5].m_obj;
lean_object* v___y_1010_ = stack[6].m_obj;
lean_object* v___y_1011_ = stack[7].m_obj;
lean_object* v_res_1069_;
v_res_1069_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1004_, v_data_1005_, v_ref_1006_, v_msg_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object* v_oldTraces_1070_, lean_object* v_data_1071_, lean_object* v_ref_1072_, lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1070_, v_data_1071_, v_ref_1072_, v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1079_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(lean_object* v_x_1080_){
_start:
{
if (lean_obj_tag(v_x_1080_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
v_a_1082_ = lean_ctor_get(v_x_1080_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v_x_1080_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v_x_1080_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
lean_ctor_set_tag(v___x_1084_, 1);
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
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
v_a_1090_ = lean_ctor_get(v_x_1080_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1080_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v_x_1080_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v_x_1080_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 0);
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1080_ = stack[0].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_1080_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg___boxed(lean_object* v_x_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_1099_);
return v_res_1101_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object* v_e_1102_){
_start:
{
if (lean_obj_tag(v_e_1102_) == 0)
{
uint8_t v___x_1103_; 
v___x_1103_ = 2;
return v___x_1103_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = 0;
return v___x_1104_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1102_ = stack[0].m_obj;
uint8_t v_res_1105_;
v_res_1105_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_e_1102_);
stack->m_num = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object* v_e_1106_){
_start:
{
uint8_t v_res_1107_; lean_object* v_r_1108_; 
v_res_1107_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_e_1106_);
lean_dec_ref(v_e_1106_);
v_r_1108_ = lean_box(v_res_1107_);
return v_r_1108_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1112_; double v___x_1113_; 
v___x_1112_ = lean_unsigned_to_nat(1000u);
v___x_1113_ = lean_float_of_nat(v___x_1112_);
return v___x_1113_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_cls_1114_, uint8_t v_collapsed_1115_, lean_object* v_tag_1116_, lean_object* v_opts_1117_, uint8_t v_clsEnabled_1118_, lean_object* v_oldTraces_1119_, lean_object* v_msg_1120_, lean_object* v_resStartStop_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v_fst_1127_; lean_object* v_snd_1128_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v_data_1132_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; lean_object* v___y_1140_; lean_object* v_a_1141_; uint8_t v___y_1156_; double v___y_1188_; 
v_fst_1127_ = lean_ctor_get(v_resStartStop_1121_, 0);
lean_inc(v_fst_1127_);
v_snd_1128_ = lean_ctor_get(v_resStartStop_1121_, 1);
lean_inc(v_snd_1128_);
lean_dec_ref(v_resStartStop_1121_);
v_fst_1135_ = lean_ctor_get(v_snd_1128_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v_snd_1128_, 1);
lean_inc(v_snd_1136_);
lean_dec(v_snd_1128_);
v___x_1137_ = l_Lean_trace_profiler;
v___x_1138_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1117_, v___x_1137_);
if (v___x_1138_ == 0)
{
v___y_1156_ = v___x_1138_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1193_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1194_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1117_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v___x_1196_; double v___x_1197_; double v___x_1198_; double v___x_1199_; 
v___x_1195_ = l_Lean_trace_profiler_threshold;
v___x_1196_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1117_, v___x_1195_);
v___x_1197_ = lean_float_of_nat(v___x_1196_);
v___x_1198_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_1199_ = lean_float_div(v___x_1197_, v___x_1198_);
v___y_1188_ = v___x_1199_;
goto v___jp_1187_;
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; double v___x_1202_; 
v___x_1200_ = l_Lean_trace_profiler_threshold;
v___x_1201_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1117_, v___x_1200_);
v___x_1202_ = lean_float_of_nat(v___x_1201_);
v___y_1188_ = v___x_1202_;
goto v___jp_1187_;
}
}
v___jp_1129_:
{
lean_object* v___x_1133_; 
lean_inc(v___y_1130_);
v___x_1133_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1119_, v_data_1132_, v___y_1130_, v___y_1131_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; 
lean_dec_ref_known(v___x_1133_, 1);
v___x_1134_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1127_);
return v___x_1134_;
}
else
{
lean_dec(v_fst_1127_);
return v___x_1133_;
}
}
v___jp_1139_:
{
uint8_t v_result_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; double v___x_1145_; lean_object* v_data_1146_; 
v_result_1142_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_fst_1127_);
v___x_1143_ = lean_box(v_result_1142_);
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
v___x_1145_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_1116_);
lean_inc_ref(v___x_1144_);
lean_inc(v_cls_1114_);
v_data_1146_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1146_, 0, v_cls_1114_);
lean_ctor_set(v_data_1146_, 1, v___x_1144_);
lean_ctor_set(v_data_1146_, 2, v_tag_1116_);
lean_ctor_set_float(v_data_1146_, sizeof(void*)*3, v___x_1145_);
lean_ctor_set_float(v_data_1146_, sizeof(void*)*3 + 8, v___x_1145_);
lean_ctor_set_uint8(v_data_1146_, sizeof(void*)*3 + 16, v_collapsed_1115_);
if (v___x_1138_ == 0)
{
lean_dec_ref_known(v___x_1144_, 1);
lean_dec(v_snd_1136_);
lean_dec(v_fst_1135_);
lean_dec_ref(v_tag_1116_);
lean_dec(v_cls_1114_);
v___y_1130_ = v___y_1140_;
v___y_1131_ = v_a_1141_;
v_data_1132_ = v_data_1146_;
goto v___jp_1129_;
}
else
{
lean_object* v_data_1147_; double v___x_1148_; double v___x_1149_; 
lean_dec_ref_known(v_data_1146_, 3);
v_data_1147_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1147_, 0, v_cls_1114_);
lean_ctor_set(v_data_1147_, 1, v___x_1144_);
lean_ctor_set(v_data_1147_, 2, v_tag_1116_);
v___x_1148_ = lean_unbox_float(v_fst_1135_);
lean_dec(v_fst_1135_);
lean_ctor_set_float(v_data_1147_, sizeof(void*)*3, v___x_1148_);
v___x_1149_ = lean_unbox_float(v_snd_1136_);
lean_dec(v_snd_1136_);
lean_ctor_set_float(v_data_1147_, sizeof(void*)*3 + 8, v___x_1149_);
lean_ctor_set_uint8(v_data_1147_, sizeof(void*)*3 + 16, v_collapsed_1115_);
v___y_1130_ = v___y_1140_;
v___y_1131_ = v_a_1141_;
v_data_1132_ = v_data_1147_;
goto v___jp_1129_;
}
}
v___jp_1150_:
{
lean_object* v_ref_1151_; lean_object* v___x_1152_; 
v_ref_1151_ = lean_ctor_get(v___y_1124_, 2);
lean_inc(v___y_1125_);
lean_inc_ref(v___y_1124_);
lean_inc(v___y_1123_);
lean_inc_ref(v___y_1122_);
lean_inc(v_fst_1127_);
v___x_1152_ = lean_apply_6(v_msg_1120_, v_fst_1127_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, lean_box(0));
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___y_1140_ = v_ref_1151_;
v_a_1141_ = v_a_1153_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1154_; 
lean_dec_ref_known(v___x_1152_, 1);
v___x_1154_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_1140_ = v_ref_1151_;
v_a_1141_ = v___x_1154_;
goto v___jp_1139_;
}
}
v___jp_1155_:
{
if (v_clsEnabled_1118_ == 0)
{
if (v___y_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v_traceState_1158_; lean_object* v_env_1159_; lean_object* v_nextMacroScope_1160_; lean_object* v_ngen_1161_; lean_object* v_auxDeclNGen_1162_; lean_object* v_cache_1163_; lean_object* v_recordedDeps_1164_; lean_object* v_messages_1165_; lean_object* v_infoState_1166_; lean_object* v_snapshotTasks_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v_snd_1136_);
lean_dec(v_fst_1135_);
lean_dec_ref(v_msg_1120_);
lean_dec_ref(v_tag_1116_);
lean_dec(v_cls_1114_);
v___x_1157_ = lean_st_ref_take(v___y_1125_);
v_traceState_1158_ = lean_ctor_get(v___x_1157_, 4);
v_env_1159_ = lean_ctor_get(v___x_1157_, 0);
v_nextMacroScope_1160_ = lean_ctor_get(v___x_1157_, 1);
v_ngen_1161_ = lean_ctor_get(v___x_1157_, 2);
v_auxDeclNGen_1162_ = lean_ctor_get(v___x_1157_, 3);
v_cache_1163_ = lean_ctor_get(v___x_1157_, 5);
v_recordedDeps_1164_ = lean_ctor_get(v___x_1157_, 6);
v_messages_1165_ = lean_ctor_get(v___x_1157_, 7);
v_infoState_1166_ = lean_ctor_get(v___x_1157_, 8);
v_snapshotTasks_1167_ = lean_ctor_get(v___x_1157_, 9);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1169_ = v___x_1157_;
v_isShared_1170_ = v_isSharedCheck_1186_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_snapshotTasks_1167_);
lean_inc(v_infoState_1166_);
lean_inc(v_messages_1165_);
lean_inc(v_recordedDeps_1164_);
lean_inc(v_cache_1163_);
lean_inc(v_traceState_1158_);
lean_inc(v_auxDeclNGen_1162_);
lean_inc(v_ngen_1161_);
lean_inc(v_nextMacroScope_1160_);
lean_inc(v_env_1159_);
lean_dec(v___x_1157_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1186_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
uint64_t v_tid_1171_; lean_object* v_traces_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1185_; 
v_tid_1171_ = lean_ctor_get_uint64(v_traceState_1158_, sizeof(void*)*1);
v_traces_1172_ = lean_ctor_get(v_traceState_1158_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_traceState_1158_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1174_ = v_traceState_1158_;
v_isShared_1175_ = v_isSharedCheck_1185_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_traces_1172_);
lean_dec(v_traceState_1158_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1185_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1176_; lean_object* v___x_1178_; 
v___x_1176_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1119_, v_traces_1172_);
lean_dec_ref(v_traces_1172_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1176_);
v___x_1178_ = v___x_1174_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1176_);
lean_ctor_set_uint64(v_reuseFailAlloc_1184_, sizeof(void*)*1, v_tid_1171_);
v___x_1178_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 4, v___x_1178_);
v___x_1180_ = v___x_1169_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_env_1159_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_nextMacroScope_1160_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_ngen_1161_);
lean_ctor_set(v_reuseFailAlloc_1183_, 3, v_auxDeclNGen_1162_);
lean_ctor_set(v_reuseFailAlloc_1183_, 4, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1183_, 5, v_cache_1163_);
lean_ctor_set(v_reuseFailAlloc_1183_, 6, v_recordedDeps_1164_);
lean_ctor_set(v_reuseFailAlloc_1183_, 7, v_messages_1165_);
lean_ctor_set(v_reuseFailAlloc_1183_, 8, v_infoState_1166_);
lean_ctor_set(v_reuseFailAlloc_1183_, 9, v_snapshotTasks_1167_);
v___x_1180_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_st_ref_put(v___y_1125_, v___x_1180_);
v___x_1182_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1127_);
return v___x_1182_;
}
}
}
}
}
else
{
goto v___jp_1150_;
}
}
else
{
goto v___jp_1150_;
}
}
v___jp_1187_:
{
double v___x_1189_; double v___x_1190_; double v___x_1191_; uint8_t v___x_1192_; 
v___x_1189_ = lean_unbox_float(v_snd_1136_);
v___x_1190_ = lean_unbox_float(v_fst_1135_);
v___x_1191_ = lean_float_sub(v___x_1189_, v___x_1190_);
v___x_1192_ = lean_float_decLt(v___y_1188_, v___x_1191_);
v___y_1156_ = v___x_1192_;
goto v___jp_1155_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1114_ = stack[0].m_obj;
uint8_t v_collapsed_1115_ = stack[1].m_num;
lean_object* v_tag_1116_ = stack[2].m_obj;
lean_object* v_opts_1117_ = stack[3].m_obj;
uint8_t v_clsEnabled_1118_ = stack[4].m_num;
lean_object* v_oldTraces_1119_ = stack[5].m_obj;
lean_object* v_msg_1120_ = stack[6].m_obj;
lean_object* v_resStartStop_1121_ = stack[7].m_obj;
lean_object* v___y_1122_ = stack[8].m_obj;
lean_object* v___y_1123_ = stack[9].m_obj;
lean_object* v___y_1124_ = stack[10].m_obj;
lean_object* v___y_1125_ = stack[11].m_obj;
lean_object* v_res_1203_;
v_res_1203_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1114_, v_collapsed_1115_, v_tag_1116_, v_opts_1117_, v_clsEnabled_1118_, v_oldTraces_1119_, v_msg_1120_, v_resStartStop_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
stack->m_obj
 = v_res_1203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_cls_1204_, lean_object* v_collapsed_1205_, lean_object* v_tag_1206_, lean_object* v_opts_1207_, lean_object* v_clsEnabled_1208_, lean_object* v_oldTraces_1209_, lean_object* v_msg_1210_, lean_object* v_resStartStop_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
uint8_t v_collapsed_boxed_1217_; uint8_t v_clsEnabled_boxed_1218_; lean_object* v_res_1219_; 
v_collapsed_boxed_1217_ = lean_unbox(v_collapsed_1205_);
v_clsEnabled_boxed_1218_ = lean_unbox(v_clsEnabled_1208_);
v_res_1219_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1204_, v_collapsed_boxed_1217_, v_tag_1206_, v_opts_1207_, v_clsEnabled_boxed_1218_, v_oldTraces_1209_, v_msg_1210_, v_resStartStop_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec_ref(v_opts_1207_);
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_unsigned_to_nat(16u);
v___x_1227_ = lean_mk_array(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1);
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1228_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1232_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1233_ = 1;
v___x_1234_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1234_, 0, v___x_1232_);
lean_ctor_set(v___x_1234_, 1, v___x_1231_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*2, v___x_1233_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_unsigned_to_nat(32u);
v___x_1236_ = lean_mk_empty_array_with_capacity(v___x_1235_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
size_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1238_ = ((size_t)5ULL);
v___x_1239_ = lean_unsigned_to_nat(0u);
v___x_1240_ = lean_unsigned_to_nat(32u);
v___x_1241_ = lean_mk_empty_array_with_capacity(v___x_1240_);
v___x_1242_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7);
v___x_1243_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___x_1241_);
lean_ctor_set(v___x_1243_, 2, v___x_1239_);
lean_ctor_set(v___x_1243_, 3, v___x_1239_);
lean_ctor_set_usize(v___x_1243_, 4, v___x_1238_);
return v___x_1243_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1245_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
lean_ctor_set(v___x_1246_, 2, v___x_1245_);
lean_ctor_set(v___x_1246_, 3, v___x_1244_);
return v___x_1246_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = lean_unsigned_to_nat(0u);
v___x_1248_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
lean_ctor_set(v___x_1249_, 1, v___x_1247_);
return v___x_1249_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9);
v___x_1251_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v___x_1250_);
return v___x_1252_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_declName_1253_, lean_object* v_as_1254_, size_t v_i_1255_, size_t v_stop_1256_, lean_object* v_b_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_usize_dec_eq(v_i_1255_, v_stop_1256_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_array_uget_borrowed(v_as_1254_, v_i_1255_);
lean_inc(v___x_1264_);
lean_inc(v_declName_1253_);
v___x_1265_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1253_, v___x_1264_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; size_t v___x_1267_; size_t v___x_1268_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v___x_1267_ = ((size_t)1ULL);
v___x_1268_ = lean_usize_add(v_i_1255_, v___x_1267_);
v_i_1255_ = v___x_1268_;
v_b_1257_ = v_a_1266_;
goto _start;
}
else
{
lean_dec(v_declName_1253_);
return v___x_1265_;
}
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_declName_1253_);
v___x_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1270_, 0, v_b_1257_);
return v___x_1270_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1253_ = stack[0].m_obj;
lean_object* v_as_1254_ = stack[1].m_obj;
size_t v_i_1255_ = stack[2].m_num;
size_t v_stop_1256_ = stack[3].m_num;
lean_object* v_b_1257_ = stack[4].m_obj;
lean_object* v___y_1258_ = stack[5].m_obj;
lean_object* v___y_1259_ = stack[6].m_obj;
lean_object* v___y_1260_ = stack[7].m_obj;
lean_object* v___y_1261_ = stack[8].m_obj;
lean_object* v_res_1271_;
v_res_1271_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1253_, v_as_1254_, v_i_1255_, v_stop_1256_, v_b_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
stack->m_obj
 = v_res_1271_;
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1274_ = l_Lean_stringToMessageData(v___x_1273_);
return v___x_1274_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v_cls_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v_cls_1287_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1288_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_1289_ = l_Lean_Name_append(v___x_1288_, v_cls_1287_);
return v___x_1289_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1290_; double v___x_1291_; 
v___x_1290_ = lean_unsigned_to_nat(1000000000u);
v___x_1291_ = lean_float_of_nat(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1307_, lean_object* v___x_1308_, lean_object* v_declName_1309_, lean_object* v_____r_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_array_get_size(v_val_1307_);
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_nat_dec_lt(v___x_1308_, v___x_1316_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
lean_dec(v_declName_1309_);
v___x_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
return v___x_1319_;
}
else
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_nat_dec_le(v___x_1316_, v___x_1316_);
if (v___x_1320_ == 0)
{
if (v___x_1318_ == 0)
{
lean_object* v___x_1321_; 
lean_dec(v_declName_1309_);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1317_);
return v___x_1321_;
}
else
{
size_t v___x_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = lean_usize_of_nat(v___x_1316_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1309_, v_val_1307_, v___x_1322_, v___x_1323_, v___x_1317_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1324_;
}
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1316_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1309_, v_val_1307_, v___x_1325_, v___x_1326_, v___x_1317_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1307_ = stack[0].m_obj;
lean_object* v___x_1308_ = stack[1].m_obj;
lean_object* v_declName_1309_ = stack[2].m_obj;
lean_object* v_____r_1310_ = stack[3].m_obj;
lean_object* v___y_1311_ = stack[4].m_obj;
lean_object* v___y_1312_ = stack[5].m_obj;
lean_object* v___y_1313_ = stack[6].m_obj;
lean_object* v___y_1314_ = stack[7].m_obj;
lean_object* v_res_1328_;
v_res_1328_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1307_, v___x_1308_, v_declName_1309_, v_____r_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
stack->m_obj
 = v_res_1328_;
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1330_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1331_ = l_Lean_stringToMessageData(v___x_1330_);
return v___x_1331_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1334_ = l_Lean_stringToMessageData(v___x_1333_);
return v___x_1334_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1337_ = l_Lean_stringToMessageData(v___x_1336_);
return v___x_1337_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1340_ = l_Lean_stringToMessageData(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1343_ = l_Lean_stringToMessageData(v___x_1342_);
return v___x_1343_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1344_, lean_object* v_mvarId_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v_toCold_1357_; lean_object* v_options_1358_; uint8_t v_hasTrace_1359_; 
v_toCold_1357_ = lean_ctor_get(v_a_1348_, 0);
v_options_1358_ = lean_ctor_get(v_toCold_1357_, 2);
v_hasTrace_1359_ = lean_ctor_get_uint8(v_options_1358_, sizeof(void*)*1);
if (v_hasTrace_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_inc(v_mvarId_1345_);
v___x_1360_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1544_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1544_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1544_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_unbox(v_a_1361_);
lean_dec(v_a_1361_);
if (v___x_1365_ == 0)
{
uint8_t v___x_1366_; lean_object* v___x_1367_; 
lean_del_object(v___x_1363_);
v___x_1366_ = 1;
lean_inc(v_mvarId_1345_);
v___x_1367_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1531_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1531_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1531_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
uint8_t v___x_1372_; 
v___x_1372_ = lean_unbox(v_a_1368_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; 
lean_del_object(v___x_1370_);
lean_inc(v_mvarId_1345_);
v___x_1373_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
if (lean_obj_tag(v_a_1374_) == 1)
{
lean_object* v_val_1375_; 
lean_dec(v_a_1368_);
lean_dec(v_mvarId_1345_);
v_val_1375_ = lean_ctor_get(v_a_1374_, 0);
lean_inc(v_val_1375_);
lean_dec_ref_known(v_a_1374_, 1);
v_mvarId_1345_ = v_val_1375_;
goto _start;
}
else
{
lean_object* v___x_1377_; 
lean_dec(v_a_1374_);
lean_inc(v_mvarId_1345_);
v___x_1377_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref_known(v___x_1377_, 1);
if (lean_obj_tag(v_a_1378_) == 1)
{
lean_object* v_val_1379_; 
lean_dec(v_a_1368_);
lean_dec(v_mvarId_1345_);
v_val_1379_ = lean_ctor_get(v_a_1378_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v_a_1378_, 1);
v_mvarId_1345_ = v_val_1379_;
goto _start;
}
else
{
lean_object* v___x_1381_; 
lean_dec(v_a_1378_);
lean_inc(v_mvarId_1345_);
v___x_1381_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1345_, v___x_1366_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
if (lean_obj_tag(v_a_1382_) == 1)
{
lean_object* v_val_1383_; 
lean_dec(v_a_1368_);
lean_dec(v_mvarId_1345_);
v_val_1383_ = lean_ctor_get(v_a_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1382_, 1);
v_mvarId_1345_ = v_val_1383_;
goto _start;
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; uint8_t v___x_1391_; uint8_t v___x_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; uint8_t v___x_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; uint8_t v___x_1398_; uint8_t v___x_1399_; uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_a_1382_);
v___x_1385_ = lean_unsigned_to_nat(100000u);
v___x_1386_ = lean_unsigned_to_nat(2u);
v___x_1387_ = 0;
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1389_, 0, v___x_1385_);
lean_ctor_set(v___x_1389_, 1, v___x_1386_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3, v___x_1390_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 1, v___x_1366_);
v___x_1391_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 2, v___x_1391_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 3, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 4, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 5, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 6, v___x_1387_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 7, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 8, v___x_1366_);
v___x_1392_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 9, v___x_1392_);
v___x_1393_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 10, v___x_1393_);
v___x_1394_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 11, v___x_1394_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 12, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 13, v___x_1366_);
v___x_1395_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 14, v___x_1395_);
v___x_1396_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 15, v___x_1396_);
v___x_1397_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 16, v___x_1397_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 17, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 18, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 19, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 20, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 21, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 22, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 23, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 24, v___x_1366_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 25, v___x_1366_);
v___x_1398_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 26, v___x_1398_);
v___x_1399_ = lean_unbox(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 27, v___x_1399_);
v___x_1400_ = lean_unbox(v_a_1368_);
lean_dec(v_a_1368_);
lean_ctor_set_uint8(v___x_1389_, sizeof(void*)*3 + 28, v___x_1400_);
v___x_1401_ = lean_unsigned_to_nat(0u);
v___x_1402_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1403_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1404_ = l_Lean_Options_empty;
v___x_1405_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1389_, v___x_1402_, v___x_1403_, v___x_1404_, v_a_1346_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
v___x_1407_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1345_);
v___x_1408_ = l_Lean_Meta_simpTargetStar(v_mvarId_1345_, v_a_1406_, v___x_1402_, v___x_1388_, v___x_1407_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1486_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1411_ = v___x_1408_;
v_isShared_1412_ = v_isSharedCheck_1486_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1408_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1486_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v_fst_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1484_; 
v_fst_1413_ = lean_ctor_get(v_a_1409_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v_a_1409_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; 
v_unused_1485_ = lean_ctor_get(v_a_1409_, 1);
lean_dec(v_unused_1485_);
v___x_1415_ = v_a_1409_;
v_isShared_1416_ = v_isSharedCheck_1484_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_fst_1413_);
lean_dec(v_a_1409_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1484_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
switch(lean_obj_tag(v_fst_1413_))
{
case 0:
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_del_object(v___x_1415_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v___x_1417_ = lean_box(0);
if (v_isShared_1412_ == 0)
{
lean_ctor_set(v___x_1411_, 0, v___x_1417_);
v___x_1419_ = v___x_1411_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
case 1:
{
lean_object* v___x_1421_; 
lean_del_object(v___x_1411_);
lean_inc(v_declName_1344_);
lean_inc(v_mvarId_1345_);
v___x_1421_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1345_, v_declName_1344_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
if (lean_obj_tag(v_a_1422_) == 1)
{
lean_object* v_val_1423_; 
lean_del_object(v___x_1415_);
lean_dec(v_mvarId_1345_);
v_val_1423_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v_a_1422_, 1);
v_mvarId_1345_ = v_val_1423_;
goto _start;
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_a_1422_);
lean_inc(v_mvarId_1345_);
v___x_1425_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1425_) == 0)
{
lean_object* v_a_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1465_; 
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1428_ = v___x_1425_;
v_isShared_1429_ = v_isSharedCheck_1465_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_a_1426_);
lean_dec(v___x_1425_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1465_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
if (lean_obj_tag(v_a_1426_) == 1)
{
lean_object* v_val_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
lean_del_object(v___x_1415_);
lean_dec(v_mvarId_1345_);
v_val_1430_ = lean_ctor_get(v_a_1426_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v_a_1426_, 1);
v___x_1431_ = lean_array_get_size(v_val_1430_);
v___x_1432_ = lean_box(0);
v___x_1433_ = lean_nat_dec_lt(v___x_1401_, v___x_1431_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1435_; 
lean_dec(v_val_1430_);
lean_dec(v_declName_1344_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1432_);
v___x_1435_ = v___x_1428_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1432_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
else
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_le(v___x_1431_, v___x_1431_);
if (v___x_1437_ == 0)
{
if (v___x_1433_ == 0)
{
lean_object* v___x_1439_; 
lean_dec(v_val_1430_);
lean_dec(v_declName_1344_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1432_);
v___x_1439_ = v___x_1428_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1432_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
else
{
size_t v___x_1441_; size_t v___x_1442_; lean_object* v___x_1443_; 
lean_del_object(v___x_1428_);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = lean_usize_of_nat(v___x_1431_);
v___x_1443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1344_, v_val_1430_, v___x_1441_, v___x_1442_, v___x_1432_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_val_1430_);
return v___x_1443_;
}
}
else
{
size_t v___x_1444_; size_t v___x_1445_; lean_object* v___x_1446_; 
lean_del_object(v___x_1428_);
v___x_1444_ = ((size_t)0ULL);
v___x_1445_ = lean_usize_of_nat(v___x_1431_);
v___x_1446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1344_, v_val_1430_, v___x_1444_, v___x_1445_, v___x_1432_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_val_1430_);
return v___x_1446_;
}
}
}
else
{
lean_object* v___x_1447_; 
lean_del_object(v___x_1428_);
lean_dec(v_a_1426_);
lean_inc(v_mvarId_1345_);
v___x_1447_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1345_, v___x_1366_, v___x_1366_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v_a_1448_; 
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref_known(v___x_1447_, 1);
if (lean_obj_tag(v_a_1448_) == 1)
{
lean_object* v_val_1449_; lean_object* v___x_1450_; 
lean_del_object(v___x_1415_);
lean_dec(v_mvarId_1345_);
v_val_1449_ = lean_ctor_get(v_a_1448_, 0);
lean_inc(v_val_1449_);
lean_dec_ref_known(v_a_1448_, 1);
v___x_1450_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1344_, v_val_1449_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
lean_dec(v_a_1448_);
lean_dec(v_declName_1344_);
v___x_1451_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v_mvarId_1345_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set_tag(v___x_1415_, 7);
lean_ctor_set(v___x_1415_, 1, v___x_1452_);
lean_ctor_set(v___x_1415_, 0, v___x_1451_);
v___x_1454_ = v___x_1415_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1454_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_1455_;
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_del_object(v___x_1415_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1457_ = lean_ctor_get(v___x_1447_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1447_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1447_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_del_object(v___x_1415_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1466_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1425_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1425_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_del_object(v___x_1415_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1474_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1421_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1421_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1482_; 
lean_del_object(v___x_1415_);
lean_del_object(v___x_1411_);
lean_dec(v_mvarId_1345_);
v_mvarId_1482_ = lean_ctor_get(v_fst_1413_, 0);
lean_inc(v_mvarId_1482_);
lean_dec_ref_known(v_fst_1413_, 1);
v_mvarId_1345_ = v_mvarId_1482_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1487_ = lean_ctor_get(v___x_1408_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1408_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1408_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1408_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1495_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1405_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1405_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_a_1368_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1503_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1381_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1381_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec(v_a_1368_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1511_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1377_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1377_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec(v_a_1368_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1519_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1373_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1373_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1529_; 
lean_dec(v_a_1368_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v___x_1527_ = lean_box(0);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1527_);
v___x_1529_ = v___x_1370_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1532_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1367_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1367_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v___x_1540_ = lean_box(0);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1540_);
v___x_1542_ = v___x_1363_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1552_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1545_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1547_ = v___x_1360_;
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1360_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1552_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1550_; 
if (v_isShared_1548_ == 0)
{
v___x_1550_ = v___x_1547_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1545_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1553_; lean_object* v___f_1554_; lean_object* v_cls_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v_a_1562_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_a_1574_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v_a_1579_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; lean_object* v___y_1588_; lean_object* v___y_1589_; lean_object* v_a_1590_; lean_object* v___y_1603_; lean_object* v___y_1604_; lean_object* v_a_1605_; lean_object* v___y_1608_; lean_object* v___y_1609_; lean_object* v_a_1610_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; 
v_inheritedTraceOptions_1553_ = lean_ctor_get(v_toCold_1357_, 11);
lean_inc(v_mvarId_1345_);
v___f_1554_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1554_, 0, v_mvarId_1345_);
v_cls_1555_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1556_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1557_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1553_, v_options_1358_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = l_Lean_trace_profiler;
v___x_1898_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1358_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v___f_1554_);
lean_inc(v_mvarId_1345_);
v___x_1899_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; uint8_t v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1901_ = lean_unbox(v_a_1900_);
lean_dec(v_a_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
lean_inc(v_mvarId_1345_);
v___x_1902_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; uint8_t v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = lean_unbox(v_a_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; 
lean_inc(v_mvarId_1345_);
v___x_1905_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
if (lean_obj_tag(v_a_1906_) == 1)
{
lean_dec(v_a_1903_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1907_; 
v_val_1907_ = lean_ctor_get(v_a_1906_, 0);
lean_inc(v_val_1907_);
lean_dec_ref_known(v_a_1906_, 1);
v_mvarId_1345_ = v_val_1907_;
goto _start;
}
else
{
lean_object* v_val_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v_val_1909_ = lean_ctor_get(v_a_1906_, 0);
lean_inc(v_val_1909_);
lean_dec_ref_known(v_a_1906_, 1);
v___x_1910_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1911_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1910_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_dec_ref_known(v___x_1911_, 1);
v_mvarId_1345_ = v_val_1909_;
goto _start;
}
else
{
lean_dec(v_val_1909_);
lean_dec(v_declName_1344_);
return v___x_1911_;
}
}
}
else
{
lean_object* v___x_1913_; 
lean_dec(v_a_1906_);
lean_inc(v_mvarId_1345_);
v___x_1913_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
if (lean_obj_tag(v_a_1914_) == 1)
{
lean_dec(v_a_1903_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1915_; 
v_val_1915_ = lean_ctor_get(v_a_1914_, 0);
lean_inc(v_val_1915_);
lean_dec_ref_known(v_a_1914_, 1);
v_mvarId_1345_ = v_val_1915_;
goto _start;
}
else
{
lean_object* v_val_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_val_1917_ = lean_ctor_get(v_a_1914_, 0);
lean_inc(v_val_1917_);
lean_dec_ref_known(v_a_1914_, 1);
v___x_1918_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1919_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1918_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_dec_ref_known(v___x_1919_, 1);
v_mvarId_1345_ = v_val_1917_;
goto _start;
}
else
{
lean_dec(v_val_1917_);
lean_dec(v_declName_1344_);
return v___x_1919_;
}
}
}
else
{
lean_object* v___x_1921_; 
lean_dec(v_a_1914_);
lean_inc(v_mvarId_1345_);
v___x_1921_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1345_, v_hasTrace_1359_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v_a_1922_; 
v_a_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_a_1922_);
lean_dec_ref_known(v___x_1921_, 1);
if (lean_obj_tag(v_a_1922_) == 1)
{
lean_dec(v_a_1903_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1923_; 
v_val_1923_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_val_1923_);
lean_dec_ref_known(v_a_1922_, 1);
v_mvarId_1345_ = v_val_1923_;
goto _start;
}
else
{
lean_object* v_val_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_val_1925_ = lean_ctor_get(v_a_1922_, 0);
lean_inc(v_val_1925_);
lean_dec_ref_known(v_a_1922_, 1);
v___x_1926_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1927_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1926_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_dec_ref_known(v___x_1927_, 1);
v_mvarId_1345_ = v_val_1925_;
goto _start;
}
else
{
lean_dec(v_val_1925_);
lean_dec(v_declName_1344_);
return v___x_1927_;
}
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; uint8_t v___x_1934_; uint8_t v___x_1935_; uint8_t v___x_1936_; uint8_t v___x_1937_; uint8_t v___x_1938_; uint8_t v___x_1939_; uint8_t v___x_1940_; uint8_t v___x_1941_; uint8_t v___x_1942_; uint8_t v___x_1943_; uint8_t v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_a_1922_);
v___x_1929_ = lean_unsigned_to_nat(100000u);
v___x_1930_ = lean_unsigned_to_nat(2u);
v___x_1931_ = 0;
v___x_1932_ = lean_box(0);
v___x_1933_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1933_, 0, v___x_1929_);
lean_ctor_set(v___x_1933_, 1, v___x_1930_);
lean_ctor_set(v___x_1933_, 2, v___x_1932_);
v___x_1934_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3, v___x_1934_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 1, v_hasTrace_1359_);
v___x_1935_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 2, v___x_1935_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 3, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 4, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 5, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 6, v___x_1931_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 7, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 8, v_hasTrace_1359_);
v___x_1936_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 9, v___x_1936_);
v___x_1937_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 10, v___x_1937_);
v___x_1938_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 11, v___x_1938_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 12, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 13, v_hasTrace_1359_);
v___x_1939_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 14, v___x_1939_);
v___x_1940_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 15, v___x_1940_);
v___x_1941_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 16, v___x_1941_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 17, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 18, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 19, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 20, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 21, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 22, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 23, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 24, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 25, v_hasTrace_1359_);
v___x_1942_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 26, v___x_1942_);
v___x_1943_ = lean_unbox(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 27, v___x_1943_);
v___x_1944_ = lean_unbox(v_a_1903_);
lean_dec(v_a_1903_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 28, v___x_1944_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1947_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1948_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1949_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*2, v_hasTrace_1359_);
v___x_1950_ = l_Lean_Options_empty;
v___x_1951_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1933_, v___x_1946_, v___x_1949_, v___x_1950_, v_a_1346_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1345_);
v___x_1954_ = l_Lean_Meta_simpTargetStar(v_mvarId_1345_, v_a_1952_, v___x_1946_, v___x_1932_, v___x_1953_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2053_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_2053_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2053_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_fst_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_2051_; 
v_fst_1959_ = lean_ctor_get(v_a_1955_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_a_1955_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v_a_1955_, 1);
lean_dec(v_unused_2052_);
v___x_1961_ = v_a_1955_;
v_isShared_1962_ = v_isSharedCheck_2051_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_fst_1959_);
lean_dec(v_a_1955_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_2051_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
switch(lean_obj_tag(v_fst_1959_))
{
case 0:
{
lean_del_object(v___x_1961_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1963_ = lean_box(0);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1963_);
v___x_1965_ = v___x_1957_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_del_object(v___x_1957_);
v___x_1967_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1968_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1967_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_1968_;
}
}
case 1:
{
lean_object* v___x_1969_; 
lean_del_object(v___x_1957_);
lean_inc(v_declName_1344_);
lean_inc(v_mvarId_1345_);
v___x_1969_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1345_, v_declName_1344_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
if (lean_obj_tag(v_a_1970_) == 1)
{
lean_del_object(v___x_1961_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1971_; 
v_val_1971_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_val_1971_);
lean_dec_ref_known(v_a_1970_, 1);
v_mvarId_1345_ = v_val_1971_;
goto _start;
}
else
{
lean_object* v_val_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_val_1973_ = lean_ctor_get(v_a_1970_, 0);
lean_inc(v_val_1973_);
lean_dec_ref_known(v_a_1970_, 1);
v___x_1974_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1975_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1974_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_dec_ref_known(v___x_1975_, 1);
v_mvarId_1345_ = v_val_1973_;
goto _start;
}
else
{
lean_dec(v_val_1973_);
lean_dec(v_declName_1344_);
return v___x_1975_;
}
}
}
else
{
lean_object* v___x_1977_; 
lean_dec(v_a_1970_);
lean_inc(v_mvarId_1345_);
v___x_1977_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2028_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_1980_ = v___x_1977_;
v_isShared_1981_ = v_isSharedCheck_2028_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2028_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
if (lean_obj_tag(v_a_1978_) == 1)
{
lean_object* v_val_1982_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; 
lean_del_object(v___x_1961_);
lean_dec(v_mvarId_1345_);
v_val_1982_ = lean_ctor_get(v_a_1978_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v_a_1978_, 1);
if (v___x_1558_ == 0)
{
v___y_1984_ = v_a_1346_;
v___y_1985_ = v_a_1347_;
v___y_1986_ = v_a_1348_;
v___y_1987_ = v_a_1349_;
goto v___jp_1983_;
}
else
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_2005_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_2004_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_dec_ref_known(v___x_2005_, 1);
v___y_1984_ = v_a_1346_;
v___y_1985_ = v_a_1347_;
v___y_1986_ = v_a_1348_;
v___y_1987_ = v_a_1349_;
goto v___jp_1983_;
}
else
{
lean_dec(v_val_1982_);
lean_del_object(v___x_1980_);
lean_dec(v_declName_1344_);
return v___x_2005_;
}
}
v___jp_1983_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v___x_1988_ = lean_array_get_size(v_val_1982_);
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_nat_dec_lt(v___x_1945_, v___x_1988_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1992_; 
lean_dec(v_val_1982_);
lean_dec(v_declName_1344_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1989_);
v___x_1992_ = v___x_1980_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1989_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_le(v___x_1988_, v___x_1988_);
if (v___x_1994_ == 0)
{
if (v___x_1990_ == 0)
{
lean_object* v___x_1996_; 
lean_dec(v_val_1982_);
lean_dec(v_declName_1344_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1989_);
v___x_1996_ = v___x_1980_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1989_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
size_t v___x_1998_; size_t v___x_1999_; lean_object* v___x_2000_; 
lean_del_object(v___x_1980_);
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = lean_usize_of_nat(v___x_1988_);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1344_, v_val_1982_, v___x_1998_, v___x_1999_, v___x_1989_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v_val_1982_);
return v___x_2000_;
}
}
else
{
size_t v___x_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
lean_del_object(v___x_1980_);
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = lean_usize_of_nat(v___x_1988_);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1344_, v_val_1982_, v___x_2001_, v___x_2002_, v___x_1989_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v_val_1982_);
return v___x_2003_;
}
}
}
}
else
{
lean_object* v___x_2006_; 
lean_del_object(v___x_1980_);
lean_dec(v_a_1978_);
lean_inc(v_mvarId_1345_);
v___x_2006_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1345_, v_hasTrace_1359_, v_hasTrace_1359_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
if (lean_obj_tag(v_a_2007_) == 1)
{
lean_del_object(v___x_1961_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_2008_; lean_object* v___x_2009_; 
v_val_2008_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_val_2008_);
lean_dec_ref_known(v_a_2007_, 1);
v___x_2009_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1344_, v_val_2008_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_2009_;
}
else
{
lean_object* v_val_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_val_2010_ = lean_ctor_get(v_a_2007_, 0);
lean_inc(v_val_2010_);
lean_dec_ref_known(v_a_2007_, 1);
v___x_2011_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_2012_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_2011_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v___x_2013_; 
lean_dec_ref_known(v___x_2012_, 1);
v___x_2013_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1344_, v_val_2010_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_2013_;
}
else
{
lean_dec(v_val_2010_);
lean_dec(v_declName_1344_);
return v___x_2012_;
}
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_dec(v_a_2007_);
lean_dec(v_declName_1344_);
v___x_2014_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_mvarId_1345_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set_tag(v___x_1961_, 7);
lean_ctor_set(v___x_1961_, 1, v___x_2015_);
lean_ctor_set(v___x_1961_, 0, v___x_2014_);
v___x_2017_ = v___x_1961_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2017_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_del_object(v___x_1961_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2020_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2006_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2006_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_del_object(v___x_1961_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2029_ = lean_ctor_get(v___x_1977_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1977_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1977_);
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
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_del_object(v___x_1961_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2037_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1969_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1969_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
default: 
{
lean_del_object(v___x_1961_);
lean_del_object(v___x_1957_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_mvarId_2045_; 
v_mvarId_2045_ = lean_ctor_get(v_fst_1959_, 0);
lean_inc(v_mvarId_2045_);
lean_dec_ref_known(v_fst_1959_, 1);
v_mvarId_1345_ = v_mvarId_2045_;
goto _start;
}
else
{
lean_object* v_mvarId_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_mvarId_2047_ = lean_ctor_get(v_fst_1959_, 0);
lean_inc(v_mvarId_2047_);
lean_dec_ref_known(v_fst_1959_, 1);
v___x_2048_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2049_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_2048_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_dec_ref_known(v___x_2049_, 1);
v_mvarId_1345_ = v_mvarId_2047_;
goto _start;
}
else
{
lean_dec(v_mvarId_2047_);
lean_dec(v_declName_1344_);
return v___x_2049_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2054_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_1954_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_1954_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
else
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2062_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2064_ = v___x_1951_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_1951_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
lean_dec(v_a_1903_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2070_ = lean_ctor_get(v___x_1921_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_1921_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_1921_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_1921_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_a_1903_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2078_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_1913_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_1913_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec(v_a_1903_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2086_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_1905_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_1905_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_dec(v_a_1903_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
goto v___jp_1354_;
}
else
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2094_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2095_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_2094_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref_known(v___x_2095_, 1);
goto v___jp_1354_;
}
else
{
return v___x_2095_;
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2096_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_1902_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_1902_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
goto v___jp_1351_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2105_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_2104_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_dec_ref_known(v___x_2105_, 1);
goto v___jp_1351_;
}
else
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_2106_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_1899_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_1899_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
goto v___jp_1618_;
}
}
else
{
goto v___jp_1618_;
}
v___jp_1559_:
{
lean_object* v___x_1563_; double v___x_1564_; double v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1563_ = lean_io_get_num_heartbeats();
v___x_1564_ = lean_float_of_nat(v___y_1560_);
v___x_1565_ = lean_float_of_nat(v___x_1563_);
v___x_1566_ = lean_box_float(v___x_1564_);
v___x_1567_ = lean_box_float(v___x_1565_);
v___x_1568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1569_, 0, v_a_1562_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1555_, v_hasTrace_1359_, v___x_1556_, v_options_1358_, v___x_1558_, v___y_1561_, v___f_1554_, v___x_1569_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_1570_;
}
v___jp_1571_:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_a_1574_);
v___y_1560_ = v___y_1572_;
v___y_1561_ = v___y_1573_;
v_a_1562_ = v___x_1575_;
goto v___jp_1559_;
}
v___jp_1576_:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v_a_1579_);
v___y_1560_ = v___y_1577_;
v___y_1561_ = v___y_1578_;
v_a_1562_ = v___x_1580_;
goto v___jp_1559_;
}
v___jp_1581_:
{
if (lean_obj_tag(v___y_1584_) == 0)
{
lean_object* v_a_1585_; 
v_a_1585_ = lean_ctor_get(v___y_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___y_1584_, 1);
v___y_1577_ = v___y_1582_;
v___y_1578_ = v___y_1583_;
v_a_1579_ = v_a_1585_;
goto v___jp_1576_;
}
else
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___y_1584_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___y_1584_, 1);
v___y_1572_ = v___y_1582_;
v___y_1573_ = v___y_1583_;
v_a_1574_ = v_a_1586_;
goto v___jp_1571_;
}
}
v___jp_1587_:
{
lean_object* v___x_1591_; double v___x_1592_; double v___x_1593_; double v___x_1594_; double v___x_1595_; double v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1591_ = lean_io_mono_nanos_now();
v___x_1592_ = lean_float_of_nat(v___y_1588_);
v___x_1593_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1594_ = lean_float_div(v___x_1592_, v___x_1593_);
v___x_1595_ = lean_float_of_nat(v___x_1591_);
v___x_1596_ = lean_float_div(v___x_1595_, v___x_1593_);
v___x_1597_ = lean_box_float(v___x_1594_);
v___x_1598_ = lean_box_float(v___x_1596_);
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v_a_1590_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1555_, v_hasTrace_1359_, v___x_1556_, v_options_1358_, v___x_1558_, v___y_1589_, v___f_1554_, v___x_1600_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
return v___x_1601_;
}
v___jp_1602_:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1606_, 0, v_a_1605_);
v___y_1588_ = v___y_1603_;
v___y_1589_ = v___y_1604_;
v_a_1590_ = v___x_1606_;
goto v___jp_1587_;
}
v___jp_1607_:
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1611_, 0, v_a_1610_);
v___y_1588_ = v___y_1608_;
v___y_1589_ = v___y_1609_;
v_a_1590_ = v___x_1611_;
goto v___jp_1587_;
}
v___jp_1612_:
{
if (lean_obj_tag(v___y_1615_) == 0)
{
lean_object* v_a_1616_; 
v_a_1616_ = lean_ctor_get(v___y_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___y_1615_, 1);
v___y_1603_ = v___y_1613_;
v___y_1604_ = v___y_1614_;
v_a_1605_ = v_a_1616_;
goto v___jp_1602_;
}
else
{
lean_object* v_a_1617_; 
v_a_1617_ = lean_ctor_get(v___y_1615_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___y_1615_, 1);
v___y_1608_ = v___y_1613_;
v___y_1609_ = v___y_1614_;
v_a_1610_ = v_a_1617_;
goto v___jp_1607_;
}
}
v___jp_1618_:
{
lean_object* v___x_1619_; 
v___x_1619_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1349_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_a_1620_);
lean_dec_ref_known(v___x_1619_, 1);
v___x_1621_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1622_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1358_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1345_);
v___x_1624_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; uint8_t v___x_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v___x_1626_ = lean_unbox(v_a_1625_);
lean_dec(v_a_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_inc(v_mvarId_1345_);
v___x_1627_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; uint8_t v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
v___x_1629_ = lean_unbox(v_a_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; 
lean_inc(v_mvarId_1345_);
v___x_1630_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
if (lean_obj_tag(v_a_1631_) == 1)
{
lean_dec(v_a_1628_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1632_; lean_object* v___x_1633_; 
v_val_1632_ = lean_ctor_get(v_a_1631_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v_a_1631_, 1);
v___x_1633_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1632_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1633_;
goto v___jp_1612_;
}
else
{
lean_object* v_val_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_val_1634_ = lean_ctor_get(v_a_1631_, 0);
lean_inc(v_val_1634_);
lean_dec_ref_known(v_a_1631_, 1);
v___x_1635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1636_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1635_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref_known(v___x_1636_, 1);
v___x_1637_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1634_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1637_;
goto v___jp_1612_;
}
else
{
lean_dec(v_val_1634_);
lean_dec(v_declName_1344_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1636_;
goto v___jp_1612_;
}
}
}
else
{
lean_object* v___x_1638_; 
lean_dec(v_a_1631_);
lean_inc(v_mvarId_1345_);
v___x_1638_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
if (lean_obj_tag(v_a_1639_) == 1)
{
lean_dec(v_a_1628_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1640_; lean_object* v___x_1641_; 
v_val_1640_ = lean_ctor_get(v_a_1639_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_a_1639_, 1);
v___x_1641_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1640_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1641_;
goto v___jp_1612_;
}
else
{
lean_object* v_val_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_val_1642_ = lean_ctor_get(v_a_1639_, 0);
lean_inc(v_val_1642_);
lean_dec_ref_known(v_a_1639_, 1);
v___x_1643_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1644_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1643_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v___x_1645_; 
lean_dec_ref_known(v___x_1644_, 1);
v___x_1645_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1642_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1645_;
goto v___jp_1612_;
}
else
{
lean_dec(v_val_1642_);
lean_dec(v_declName_1344_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1644_;
goto v___jp_1612_;
}
}
}
else
{
lean_object* v___x_1646_; 
lean_dec(v_a_1639_);
lean_inc(v_mvarId_1345_);
v___x_1646_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1345_, v_hasTrace_1359_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v___x_1646_, 1);
if (lean_obj_tag(v_a_1647_) == 1)
{
lean_dec(v_a_1628_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1648_; lean_object* v___x_1649_; 
v_val_1648_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_val_1648_);
lean_dec_ref_known(v_a_1647_, 1);
v___x_1649_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1648_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1649_;
goto v___jp_1612_;
}
else
{
lean_object* v_val_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_val_1650_ = lean_ctor_get(v_a_1647_, 0);
lean_inc(v_val_1650_);
lean_dec_ref_known(v_a_1647_, 1);
v___x_1651_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1652_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1651_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref_known(v___x_1652_, 1);
v___x_1653_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1650_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1653_;
goto v___jp_1612_;
}
else
{
lean_dec(v_val_1650_);
lean_dec(v_declName_1344_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1652_;
goto v___jp_1612_;
}
}
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; uint8_t v___x_1660_; uint8_t v___x_1661_; uint8_t v___x_1662_; uint8_t v___x_1663_; uint8_t v___x_1664_; uint8_t v___x_1665_; uint8_t v___x_1666_; uint8_t v___x_1667_; uint8_t v___x_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_dec(v_a_1647_);
v___x_1654_ = lean_unsigned_to_nat(100000u);
v___x_1655_ = lean_unsigned_to_nat(2u);
v___x_1656_ = 0;
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1658_, 0, v___x_1654_);
lean_ctor_set(v___x_1658_, 1, v___x_1655_);
lean_ctor_set(v___x_1658_, 2, v___x_1657_);
v___x_1659_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3, v___x_1659_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 1, v_hasTrace_1359_);
v___x_1660_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 2, v___x_1660_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 3, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 4, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 5, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 6, v___x_1656_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 7, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 8, v_hasTrace_1359_);
v___x_1661_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 9, v___x_1661_);
v___x_1662_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 10, v___x_1662_);
v___x_1663_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 11, v___x_1663_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 12, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 13, v_hasTrace_1359_);
v___x_1664_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 14, v___x_1664_);
v___x_1665_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 15, v___x_1665_);
v___x_1666_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 16, v___x_1666_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 17, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 18, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 19, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 20, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 21, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 22, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 23, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 24, v_hasTrace_1359_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 25, v_hasTrace_1359_);
v___x_1667_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 26, v___x_1667_);
v___x_1668_ = lean_unbox(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 27, v___x_1668_);
v___x_1669_ = lean_unbox(v_a_1628_);
lean_dec(v_a_1628_);
lean_ctor_set_uint8(v___x_1658_, sizeof(void*)*3 + 28, v___x_1669_);
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1672_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1673_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1674_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*2, v_hasTrace_1359_);
v___x_1675_ = l_Lean_Options_empty;
v___x_1676_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1658_, v___x_1671_, v___x_1674_, v___x_1675_, v_a_1346_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1345_);
v___x_1679_ = l_Lean_Meta_simpTargetStar(v_mvarId_1345_, v_a_1677_, v___x_1671_, v___x_1657_, v___x_1678_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v_fst_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1735_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v_fst_1681_ = lean_ctor_get(v_a_1680_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_a_1680_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_a_1680_, 1);
lean_dec(v_unused_1736_);
v___x_1683_ = v_a_1680_;
v_isShared_1684_ = v_isSharedCheck_1735_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_fst_1681_);
lean_dec(v_a_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1735_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
switch(lean_obj_tag(v_fst_1681_))
{
case 0:
{
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_box(0);
v___y_1603_ = v___x_1623_;
v___y_1604_ = v_a_1620_;
v_a_1605_ = v___x_1685_;
goto v___jp_1602_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1687_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1686_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1687_;
goto v___jp_1612_;
}
}
case 1:
{
lean_object* v___x_1688_; 
lean_inc(v_declName_1344_);
lean_inc(v_mvarId_1345_);
v___x_1688_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1345_, v_declName_1344_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
if (lean_obj_tag(v_a_1689_) == 1)
{
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1690_; lean_object* v___x_1691_; 
v_val_1690_ = lean_ctor_get(v_a_1689_, 0);
lean_inc(v_val_1690_);
lean_dec_ref_known(v_a_1689_, 1);
v___x_1691_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1690_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1691_;
goto v___jp_1612_;
}
else
{
lean_object* v_val_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_val_1692_ = lean_ctor_get(v_a_1689_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v_a_1689_, 1);
v___x_1693_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1694_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1693_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1695_; 
lean_dec_ref_known(v___x_1694_, 1);
v___x_1695_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1692_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1695_;
goto v___jp_1612_;
}
else
{
lean_dec(v_val_1692_);
lean_dec(v_declName_1344_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1694_;
goto v___jp_1612_;
}
}
}
else
{
lean_object* v___x_1696_; 
lean_dec(v_a_1689_);
lean_inc(v_mvarId_1345_);
v___x_1696_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
if (lean_obj_tag(v_a_1697_) == 1)
{
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v_val_1698_ = lean_ctor_get(v_a_1697_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v_a_1697_, 1);
v___x_1699_ = lean_box(0);
v___x_1700_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1698_, v___x_1670_, v_declName_1344_, v___x_1699_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_val_1698_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1700_;
goto v___jp_1612_;
}
else
{
lean_object* v_val_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_val_1701_ = lean_ctor_get(v_a_1697_, 0);
lean_inc(v_val_1701_);
lean_dec_ref_known(v_a_1697_, 1);
v___x_1702_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1703_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1702_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; lean_object* v___x_1705_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1701_, v___x_1670_, v_declName_1344_, v_a_1704_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_val_1701_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1705_;
goto v___jp_1612_;
}
else
{
lean_dec(v_val_1701_);
lean_dec(v_declName_1344_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1703_;
goto v___jp_1612_;
}
}
}
else
{
lean_object* v___x_1706_; 
lean_dec(v_a_1697_);
lean_inc(v_mvarId_1345_);
v___x_1706_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1345_, v_hasTrace_1359_, v_hasTrace_1359_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1725_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1725_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1725_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
if (lean_obj_tag(v_a_1707_) == 1)
{
lean_del_object(v___x_1709_);
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1711_; lean_object* v___x_1712_; 
v_val_1711_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_val_1711_);
lean_dec_ref_known(v_a_1707_, 1);
v___x_1712_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1344_, v_val_1711_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1712_;
goto v___jp_1612_;
}
else
{
lean_object* v_val_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v_val_1713_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v_a_1707_, 1);
v___x_1714_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1715_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1714_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; 
lean_dec_ref_known(v___x_1715_, 1);
v___x_1716_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1344_, v_val_1713_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1716_;
goto v___jp_1612_;
}
else
{
lean_dec(v_val_1713_);
lean_dec(v_declName_1344_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1715_;
goto v___jp_1612_;
}
}
}
else
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
lean_dec(v_a_1707_);
lean_dec(v_declName_1344_);
v___x_1717_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1710_ == 0)
{
lean_ctor_set_tag(v___x_1709_, 1);
lean_ctor_set(v___x_1709_, 0, v_mvarId_1345_);
v___x_1719_ = v___x_1709_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_mvarId_1345_);
v___x_1719_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1721_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 7);
lean_ctor_set(v___x_1683_, 1, v___x_1719_);
lean_ctor_set(v___x_1683_, 0, v___x_1717_);
v___x_1721_ = v___x_1683_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1721_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1722_;
goto v___jp_1612_;
}
}
}
}
}
else
{
lean_object* v_a_1726_; 
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1726_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1706_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1726_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1727_; 
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1727_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1696_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1727_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1728_; 
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1728_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1688_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1728_;
goto v___jp_1607_;
}
}
default: 
{
lean_del_object(v___x_1683_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_mvarId_1729_; lean_object* v___x_1730_; 
v_mvarId_1729_ = lean_ctor_get(v_fst_1681_, 0);
lean_inc(v_mvarId_1729_);
lean_dec_ref_known(v_fst_1681_, 1);
v___x_1730_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_mvarId_1729_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1730_;
goto v___jp_1612_;
}
else
{
lean_object* v_mvarId_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_mvarId_1731_ = lean_ctor_get(v_fst_1681_, 0);
lean_inc(v_mvarId_1731_);
lean_dec_ref_known(v_fst_1681_, 1);
v___x_1732_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1733_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1732_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref_known(v___x_1733_, 1);
v___x_1734_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_mvarId_1731_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1734_;
goto v___jp_1612_;
}
else
{
lean_dec(v_mvarId_1731_);
lean_dec(v_declName_1344_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1733_;
goto v___jp_1612_;
}
}
}
}
}
}
else
{
lean_object* v_a_1737_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1737_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1679_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1737_;
goto v___jp_1607_;
}
}
else
{
lean_object* v_a_1738_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1738_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1676_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1738_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1739_; 
lean_dec(v_a_1628_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1739_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1646_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1739_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1740_; 
lean_dec(v_a_1628_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1740_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1638_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1740_;
goto v___jp_1607_;
}
}
}
else
{
lean_object* v_a_1741_; 
lean_dec(v_a_1628_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1741_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1630_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1741_;
goto v___jp_1607_;
}
}
else
{
lean_dec(v_a_1628_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_box(0);
v___x_1743_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1742_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1743_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1744_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1745_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1744_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref_known(v___x_1745_, 1);
v___x_1747_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1746_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1747_;
goto v___jp_1612_;
}
else
{
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1745_;
goto v___jp_1612_;
}
}
}
}
else
{
lean_object* v_a_1748_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1748_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1627_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1748_;
goto v___jp_1607_;
}
}
else
{
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_box(0);
v___x_1750_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1749_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1750_;
goto v___jp_1612_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1752_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1751_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1753_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1754_;
goto v___jp_1612_;
}
else
{
v___y_1613_ = v___x_1623_;
v___y_1614_ = v_a_1620_;
v___y_1615_ = v___x_1752_;
goto v___jp_1612_;
}
}
}
}
else
{
lean_object* v_a_1755_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1755_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1624_, 1);
v___y_1608_ = v___x_1623_;
v___y_1609_ = v_a_1620_;
v_a_1610_ = v_a_1755_;
goto v___jp_1607_;
}
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1345_);
v___x_1757_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; uint8_t v___x_1759_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = lean_unbox(v_a_1758_);
lean_dec(v_a_1758_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_inc(v_mvarId_1345_);
v___x_1760_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; uint8_t v___x_1762_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = lean_unbox(v_a_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
lean_inc(v_mvarId_1345_);
v___x_1763_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
if (lean_obj_tag(v_a_1764_) == 1)
{
lean_dec(v_a_1761_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1765_; lean_object* v___x_1766_; 
v_val_1765_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1765_);
lean_dec_ref_known(v_a_1764_, 1);
v___x_1766_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1765_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1766_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_val_1767_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v_a_1764_, 1);
v___x_1768_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1769_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1768_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1769_, 1);
v___x_1770_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1767_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1770_;
goto v___jp_1581_;
}
else
{
lean_dec(v_val_1767_);
lean_dec(v_declName_1344_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1769_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1771_; 
lean_dec(v_a_1764_);
lean_inc(v_mvarId_1345_);
v___x_1771_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
if (lean_obj_tag(v_a_1772_) == 1)
{
lean_dec(v_a_1761_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1773_; lean_object* v___x_1774_; 
v_val_1773_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v_a_1772_, 1);
v___x_1774_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1773_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1774_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_val_1775_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_val_1775_);
lean_dec_ref_known(v_a_1772_, 1);
v___x_1776_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1777_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1776_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v___x_1778_; 
lean_dec_ref_known(v___x_1777_, 1);
v___x_1778_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1775_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1778_;
goto v___jp_1581_;
}
else
{
lean_dec(v_val_1775_);
lean_dec(v_declName_1344_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1777_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1779_; 
lean_dec(v_a_1772_);
lean_inc(v_mvarId_1345_);
v___x_1779_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1345_, v___x_1622_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
if (lean_obj_tag(v_a_1780_) == 1)
{
lean_dec(v_a_1761_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1781_; lean_object* v___x_1782_; 
v_val_1781_ = lean_ctor_get(v_a_1780_, 0);
lean_inc(v_val_1781_);
lean_dec_ref_known(v_a_1780_, 1);
v___x_1782_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1781_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1782_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v_val_1783_ = lean_ctor_get(v_a_1780_, 0);
lean_inc(v_val_1783_);
lean_dec_ref_known(v_a_1780_, 1);
v___x_1784_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1785_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1784_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v___x_1786_; 
lean_dec_ref_known(v___x_1785_, 1);
v___x_1786_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1783_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1786_;
goto v___jp_1581_;
}
else
{
lean_dec(v_val_1783_);
lean_dec(v_declName_1344_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1785_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; uint8_t v___x_1793_; uint8_t v___x_1794_; uint8_t v___x_1795_; uint8_t v___x_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; uint8_t v___x_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; uint8_t v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v_a_1780_);
v___x_1787_ = lean_unsigned_to_nat(100000u);
v___x_1788_ = lean_unsigned_to_nat(2u);
v___x_1789_ = 0;
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1791_, 0, v___x_1787_);
lean_ctor_set(v___x_1791_, 1, v___x_1788_);
lean_ctor_set(v___x_1791_, 2, v___x_1790_);
v___x_1792_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3, v___x_1792_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 1, v___x_1622_);
v___x_1793_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 2, v___x_1793_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 3, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 4, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 5, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 6, v___x_1789_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 7, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 8, v___x_1622_);
v___x_1794_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 9, v___x_1794_);
v___x_1795_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 10, v___x_1795_);
v___x_1796_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 11, v___x_1796_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 12, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 13, v___x_1622_);
v___x_1797_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 14, v___x_1797_);
v___x_1798_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 15, v___x_1798_);
v___x_1799_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 16, v___x_1799_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 17, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 18, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 19, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 20, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 21, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 22, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 23, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 24, v___x_1622_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 25, v___x_1622_);
v___x_1800_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 26, v___x_1800_);
v___x_1801_ = lean_unbox(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 27, v___x_1801_);
v___x_1802_ = lean_unbox(v_a_1761_);
lean_dec(v_a_1761_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*3 + 28, v___x_1802_);
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1805_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1806_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1807_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
lean_ctor_set_uint8(v___x_1807_, sizeof(void*)*2, v___x_1622_);
v___x_1808_ = l_Lean_Options_empty;
v___x_1809_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1791_, v___x_1804_, v___x_1807_, v___x_1808_, v_a_1346_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1345_);
v___x_1812_ = l_Lean_Meta_simpTargetStar(v_mvarId_1345_, v_a_1810_, v___x_1804_, v___x_1790_, v___x_1811_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v_fst_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1868_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1812_, 1);
v_fst_1814_ = lean_ctor_get(v_a_1813_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_a_1813_);
if (v_isSharedCheck_1868_ == 0)
{
lean_object* v_unused_1869_; 
v_unused_1869_ = lean_ctor_get(v_a_1813_, 1);
lean_dec(v_unused_1869_);
v___x_1816_ = v_a_1813_;
v_isShared_1817_ = v_isSharedCheck_1868_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_fst_1814_);
lean_dec(v_a_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1868_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
switch(lean_obj_tag(v_fst_1814_))
{
case 0:
{
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_box(0);
v___y_1577_ = v___x_1756_;
v___y_1578_ = v_a_1620_;
v_a_1579_ = v___x_1818_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1820_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1819_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1820_;
goto v___jp_1581_;
}
}
case 1:
{
lean_object* v___x_1821_; 
lean_inc(v_declName_1344_);
lean_inc(v_mvarId_1345_);
v___x_1821_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1345_, v_declName_1344_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1821_, 1);
if (lean_obj_tag(v_a_1822_) == 1)
{
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1823_; lean_object* v___x_1824_; 
v_val_1823_ = lean_ctor_get(v_a_1822_, 0);
lean_inc(v_val_1823_);
lean_dec_ref_known(v_a_1822_, 1);
v___x_1824_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1823_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1824_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v_val_1825_ = lean_ctor_get(v_a_1822_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v_a_1822_, 1);
v___x_1826_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1827_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1826_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v___x_1828_; 
lean_dec_ref_known(v___x_1827_, 1);
v___x_1828_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_val_1825_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1828_;
goto v___jp_1581_;
}
else
{
lean_dec(v_val_1825_);
lean_dec(v_declName_1344_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1827_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1829_; 
lean_dec(v_a_1822_);
lean_inc(v_mvarId_1345_);
v___x_1829_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1829_, 1);
if (lean_obj_tag(v_a_1830_) == 1)
{
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_val_1831_ = lean_ctor_get(v_a_1830_, 0);
lean_inc(v_val_1831_);
lean_dec_ref_known(v_a_1830_, 1);
v___x_1832_ = lean_box(0);
v___x_1833_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1831_, v___x_1803_, v_declName_1344_, v___x_1832_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_val_1831_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1833_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_val_1834_ = lean_ctor_get(v_a_1830_, 0);
lean_inc(v_val_1834_);
lean_dec_ref_known(v_a_1830_, 1);
v___x_1835_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1836_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1835_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1838_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
v___x_1838_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1834_, v___x_1803_, v_declName_1344_, v_a_1837_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_val_1834_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1838_;
goto v___jp_1581_;
}
else
{
lean_dec(v_val_1834_);
lean_dec(v_declName_1344_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1836_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1839_; 
lean_dec(v_a_1830_);
lean_inc(v_mvarId_1345_);
v___x_1839_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1345_, v___x_1622_, v___x_1622_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1858_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1858_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1858_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
if (lean_obj_tag(v_a_1840_) == 1)
{
lean_del_object(v___x_1842_);
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_val_1844_; lean_object* v___x_1845_; 
v_val_1844_ = lean_ctor_get(v_a_1840_, 0);
lean_inc(v_val_1844_);
lean_dec_ref_known(v_a_1840_, 1);
v___x_1845_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1344_, v_val_1844_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1845_;
goto v___jp_1581_;
}
else
{
lean_object* v_val_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v_val_1846_ = lean_ctor_get(v_a_1840_, 0);
lean_inc(v_val_1846_);
lean_dec_ref_known(v_a_1840_, 1);
v___x_1847_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1848_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1847_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v___x_1849_; 
lean_dec_ref_known(v___x_1848_, 1);
v___x_1849_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1344_, v_val_1846_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1849_;
goto v___jp_1581_;
}
else
{
lean_dec(v_val_1846_);
lean_dec(v_declName_1344_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1848_;
goto v___jp_1581_;
}
}
}
else
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec(v_a_1840_);
lean_dec(v_declName_1344_);
v___x_1850_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 1);
lean_ctor_set(v___x_1842_, 0, v_mvarId_1345_);
v___x_1852_ = v___x_1842_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_mvarId_1345_);
v___x_1852_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 7);
lean_ctor_set(v___x_1816_, 1, v___x_1852_);
lean_ctor_set(v___x_1816_, 0, v___x_1850_);
v___x_1854_ = v___x_1816_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1854_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1855_;
goto v___jp_1581_;
}
}
}
}
}
else
{
lean_object* v_a_1859_; 
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1859_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1839_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1859_;
goto v___jp_1571_;
}
}
}
else
{
lean_object* v_a_1860_; 
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1860_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1860_);
lean_dec_ref_known(v___x_1829_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1860_;
goto v___jp_1571_;
}
}
}
else
{
lean_object* v_a_1861_; 
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1861_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1821_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1861_;
goto v___jp_1571_;
}
}
default: 
{
lean_del_object(v___x_1816_);
lean_dec(v_mvarId_1345_);
if (v___x_1558_ == 0)
{
lean_object* v_mvarId_1862_; lean_object* v___x_1863_; 
v_mvarId_1862_ = lean_ctor_get(v_fst_1814_, 0);
lean_inc(v_mvarId_1862_);
lean_dec_ref_known(v_fst_1814_, 1);
v___x_1863_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_mvarId_1862_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1863_;
goto v___jp_1581_;
}
else
{
lean_object* v_mvarId_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_mvarId_1864_ = lean_ctor_get(v_fst_1814_, 0);
lean_inc(v_mvarId_1864_);
lean_dec_ref_known(v_fst_1814_, 1);
v___x_1865_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1866_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1865_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v___x_1867_; 
lean_dec_ref_known(v___x_1866_, 1);
v___x_1867_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_mvarId_1864_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1867_;
goto v___jp_1581_;
}
else
{
lean_dec(v_mvarId_1864_);
lean_dec(v_declName_1344_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1866_;
goto v___jp_1581_;
}
}
}
}
}
}
else
{
lean_object* v_a_1870_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1870_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1812_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1870_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_1871_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1871_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1809_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1871_;
goto v___jp_1571_;
}
}
}
else
{
lean_object* v_a_1872_; 
lean_dec(v_a_1761_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1872_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1779_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1872_;
goto v___jp_1571_;
}
}
}
else
{
lean_object* v_a_1873_; 
lean_dec(v_a_1761_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1873_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1771_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1873_;
goto v___jp_1571_;
}
}
}
else
{
lean_object* v_a_1874_; 
lean_dec(v_a_1761_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1874_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1763_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1874_;
goto v___jp_1571_;
}
}
else
{
lean_dec(v_a_1761_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1875_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1876_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1878_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1877_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1879_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1880_;
goto v___jp_1581_;
}
else
{
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1878_;
goto v___jp_1581_;
}
}
}
}
else
{
lean_object* v_a_1881_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1881_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1760_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1881_;
goto v___jp_1571_;
}
}
else
{
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1882_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1883_;
goto v___jp_1581_;
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1885_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1555_, v___x_1884_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1886_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1887_;
goto v___jp_1581_;
}
else
{
v___y_1582_ = v___x_1756_;
v___y_1583_ = v_a_1620_;
v___y_1584_ = v___x_1885_;
goto v___jp_1581_;
}
}
}
}
else
{
lean_object* v_a_1888_; 
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1888_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1757_, 1);
v___y_1572_ = v___x_1756_;
v___y_1573_ = v_a_1620_;
v_a_1574_ = v_a_1888_;
goto v___jp_1571_;
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec_ref(v___f_1554_);
lean_dec(v_mvarId_1345_);
lean_dec(v_declName_1344_);
v_a_1889_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1619_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1619_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
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
return v___x_1894_;
}
}
}
}
}
v___jp_1351_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
v___jp_1354_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_box(0);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
return v___x_1356_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1344_ = stack[0].m_obj;
lean_object* v_mvarId_1345_ = stack[1].m_obj;
lean_object* v_a_1346_ = stack[2].m_obj;
lean_object* v_a_1347_ = stack[3].m_obj;
lean_object* v_a_1348_ = stack[4].m_obj;
lean_object* v_a_1349_ = stack[5].m_obj;
lean_object* v_res_2114_;
v_res_2114_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1344_, v_mvarId_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
stack->m_obj
 = v_res_2114_;
}
lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2115_, lean_object* v_as_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
if (lean_obj_tag(v_as_2116_) == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec(v_declName_2115_);
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
else
{
lean_object* v_head_2124_; lean_object* v_tail_2125_; lean_object* v___x_2126_; 
v_head_2124_ = lean_ctor_get(v_as_2116_, 0);
lean_inc(v_head_2124_);
v_tail_2125_ = lean_ctor_get(v_as_2116_, 1);
lean_inc(v_tail_2125_);
lean_dec_ref_known(v_as_2116_, 2);
lean_inc(v_declName_2115_);
v___x_2126_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2115_, v_head_2124_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_dec_ref_known(v___x_2126_, 1);
v_as_2116_ = v_tail_2125_;
goto _start;
}
else
{
lean_dec(v_tail_2125_);
lean_dec(v_declName_2115_);
return v___x_2126_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2115_ = stack[0].m_obj;
lean_object* v_as_2116_ = stack[1].m_obj;
lean_object* v___y_2117_ = stack[2].m_obj;
lean_object* v___y_2118_ = stack[3].m_obj;
lean_object* v___y_2119_ = stack[4].m_obj;
lean_object* v___y_2120_ = stack[5].m_obj;
lean_object* v_res_2128_;
v_res_2128_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2115_, v_as_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
stack->m_obj
 = v_res_2128_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2129_, lean_object* v_as_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2129_, v_as_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2137_, lean_object* v_as_2138_, lean_object* v_i_2139_, lean_object* v_stop_2140_, lean_object* v_b_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
size_t v_i_boxed_2147_; size_t v_stop_boxed_2148_; lean_object* v_res_2149_; 
v_i_boxed_2147_ = lean_unbox_usize(v_i_2139_);
lean_dec(v_i_2139_);
v_stop_boxed_2148_ = lean_unbox_usize(v_stop_2140_);
lean_dec(v_stop_2140_);
v_res_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2137_, v_as_2138_, v_i_boxed_2147_, v_stop_boxed_2148_, v_b_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec_ref(v_as_2138_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2150_, lean_object* v___x_2151_, lean_object* v_declName_2152_, lean_object* v_____r_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2150_, v___x_2151_, v_declName_2152_, v_____r_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___x_2151_);
lean_dec_ref(v_val_2150_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2160_, lean_object* v_mvarId_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2160_, v_mvarId_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
return v_res_2167_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_00_u03b1_2168_, lean_object* v_x_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_2169_);
return v___x_2175_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2169_ = stack[1].m_obj;
lean_object* v___y_2170_ = stack[2].m_obj;
lean_object* v___y_2171_ = stack[3].m_obj;
lean_object* v___y_2172_ = stack[4].m_obj;
lean_object* v___y_2173_ = stack[5].m_obj;
lean_object* v_res_2176_;
v_res_2176_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_box(0), v_x_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
stack->m_obj
 = v_res_2176_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_x_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_00_u03b1_2177_, v_x_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2184_;
}
}
lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2185_, uint8_t v_skipRealize_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v___x_2189_; lean_object* v_env_2190_; uint8_t v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2189_ = lean_st_ref_get(v___y_2187_);
v_env_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc_ref(v_env_2190_);
lean_dec(v___x_2189_);
v___x_2191_ = l_Lean_Environment_contains(v_env_2190_, v_constName_2185_, v_skipRealize_2186_);
v___x_2192_ = lean_box(v___x_2191_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2185_ = stack[0].m_obj;
uint8_t v_skipRealize_2186_ = stack[1].m_num;
lean_object* v___y_2187_ = stack[2].m_obj;
lean_object* v_res_2194_;
v_res_2194_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2185_, v_skipRealize_2186_, v___y_2187_);
stack->m_obj
 = v_res_2194_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2195_, lean_object* v_skipRealize_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v_skipRealize_boxed_2199_; lean_object* v_res_2200_; 
v_skipRealize_boxed_2199_ = lean_unbox(v_skipRealize_2196_);
v_res_2200_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2195_, v_skipRealize_boxed_2199_, v___y_2197_);
lean_dec(v___y_2197_);
return v_res_2200_;
}
}
lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2201_, uint8_t v_skipRealize_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2201_, v_skipRealize_2202_, v___y_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT void l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2201_ = stack[0].m_obj;
uint8_t v_skipRealize_2202_ = stack[1].m_num;
lean_object* v___y_2203_ = stack[2].m_obj;
lean_object* v___y_2204_ = stack[3].m_obj;
lean_object* v___y_2205_ = stack[4].m_obj;
lean_object* v___y_2206_ = stack[5].m_obj;
lean_object* v_res_2209_;
v_res_2209_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2201_, v_skipRealize_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
stack->m_obj
 = v_res_2209_;
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2210_, lean_object* v_skipRealize_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
uint8_t v_skipRealize_boxed_2217_; lean_object* v_res_2218_; 
v_skipRealize_boxed_2217_ = lean_unbox(v_skipRealize_2211_);
v_res_2218_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2210_, v_skipRealize_boxed_2217_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
return v_res_2218_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2219_, lean_object* v___x_2220_, lean_object* v___x_2221_, lean_object* v_snd_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; 
lean_inc_ref(v_snd_2219_);
v___x_2228_ = l_Lean_Meta_mkCongrArg(v_snd_2219_, v___x_2220_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___x_2230_ = l_Lean_Expr_app___override(v_snd_2219_, v___x_2221_);
v___x_2231_ = l_Lean_MVarId_replaceTargetEq(v_snd_2222_, v___x_2230_, v_a_2229_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2231_;
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_snd_2222_);
lean_dec_ref(v___x_2221_);
lean_dec_ref(v_snd_2219_);
v_a_2232_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2228_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2228_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_2219_ = stack[0].m_obj;
lean_object* v___x_2220_ = stack[1].m_obj;
lean_object* v___x_2221_ = stack[2].m_obj;
lean_object* v_snd_2222_ = stack[3].m_obj;
lean_object* v___y_2223_ = stack[4].m_obj;
lean_object* v___y_2224_ = stack[5].m_obj;
lean_object* v___y_2225_ = stack[6].m_obj;
lean_object* v___y_2226_ = stack[7].m_obj;
lean_object* v_res_2240_;
v_res_2240_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2219_, v___x_2220_, v___x_2221_, v_snd_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
stack->m_obj
 = v_res_2240_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2241_, lean_object* v___x_2242_, lean_object* v___x_2243_, lean_object* v_snd_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_res_2250_; 
v_res_2250_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2241_, v___x_2242_, v___x_2243_, v_snd_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
return v_res_2250_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2257_ = l_Lean_stringToMessageData(v___x_2256_);
return v___x_2257_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2260_ = l_Lean_stringToMessageData(v___x_2259_);
return v___x_2260_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2263_ = l_Lean_stringToMessageData(v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2269_ = l_Lean_stringToMessageData(v___x_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2272_ = l_Lean_stringToMessageData(v___x_2271_);
return v___x_2272_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2273_, lean_object* v___x_2274_, lean_object* v_cls_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
lean_inc(v_mvarId_2273_);
v___x_2281_ = l_Lean_MVarId_getType(v_mvarId_2273_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
v___x_2283_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2282_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v_fst_2285_; lean_object* v_snd_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2440_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v_fst_2285_ = lean_ctor_get(v_a_2284_, 0);
v_snd_2286_ = lean_ctor_get(v_a_2284_, 1);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_a_2284_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2288_ = v_a_2284_;
v_isShared_2289_ = v_isSharedCheck_2440_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_snd_2286_);
lean_inc(v_fst_2285_);
lean_dec(v_a_2284_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2440_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v_dummy_2295_; lean_object* v_nargs_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; uint8_t v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2342_; lean_object* v___y_2343_; lean_object* v___y_2344_; lean_object* v___y_2345_; uint8_t v___x_2414_; lean_object* v___x_2415_; lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2439_; 
v___x_2290_ = l_Lean_Expr_getAppFn(v_fst_2285_);
v___x_2291_ = l_Lean_Expr_constName_x21(v___x_2290_);
v___x_2292_ = l_Lean_Expr_constLevels_x21(v___x_2290_);
lean_dec_ref(v___x_2290_);
v___x_2293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2294_ = l_Lean_Name_str___override(v___x_2291_, v___x_2293_);
v_dummy_2295_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_2296_ = l_Lean_Expr_getAppNumArgs(v_fst_2285_);
lean_inc(v_nargs_2296_);
v___x_2297_ = lean_mk_array(v_nargs_2296_, v_dummy_2295_);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_sub(v_nargs_2296_, v___x_2298_);
lean_dec(v_nargs_2296_);
v___x_2300_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2285_, v___x_2297_, v___x_2299_);
v___x_2414_ = 1;
lean_inc(v___x_2294_);
v___x_2415_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2294_, v___x_2414_, v___y_2279_);
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2439_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2439_;
goto v_resetjp_2417_;
}
v___jp_2301_:
{
lean_object* v___x_2310_; 
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
lean_inc(v___y_2307_);
lean_inc_ref(v___y_2306_);
lean_inc_ref(v___y_2302_);
v___x_2310_ = lean_infer_type(v___y_2302_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2313_ = l_Lean_MVarId_define(v_mvarId_2273_, v___x_2312_, v_a_2311_, v___y_2302_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = l_Lean_Meta_intro1Core(v_a_2314_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v_fst_2317_; lean_object* v_snd_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_fst_2317_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_fst_2317_);
v_snd_2318_ = lean_ctor_get(v_a_2316_, 1);
lean_inc_n(v_snd_2318_, 2);
lean_dec(v_a_2316_);
v___x_2319_ = l_Lean_Expr_appFn_x21(v___y_2304_);
lean_dec_ref(v___y_2304_);
v___x_2320_ = l_Lean_mkFVar(v_fst_2317_);
v___x_2321_ = l_Lean_Expr_app___override(v___x_2319_, v___x_2320_);
v___x_2322_ = l_Lean_mkAppN(v___y_2303_, v___x_2300_);
lean_dec_ref(v___x_2300_);
v___f_2323_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2323_, 0, v_snd_2286_);
lean_closure_set(v___f_2323_, 1, v___x_2322_);
lean_closure_set(v___f_2323_, 2, v___x_2321_);
lean_closure_set(v___f_2323_, 3, v_snd_2318_);
v___x_2324_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2318_, v___f_2323_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
return v___x_2324_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec_ref(v___x_2300_);
lean_dec(v_snd_2286_);
v_a_2325_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2315_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2315_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
else
{
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec_ref(v___x_2300_);
lean_dec(v_snd_2286_);
return v___x_2313_;
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec_ref(v___x_2300_);
lean_dec(v_snd_2286_);
lean_dec(v_mvarId_2273_);
v_a_2333_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2310_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2310_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
v___jp_2341_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
lean_inc(v___x_2294_);
v___x_2346_ = l_Lean_mkConst(v___x_2294_, v___x_2292_);
lean_inc(v___y_2345_);
lean_inc_ref(v___y_2344_);
lean_inc(v___y_2343_);
lean_inc_ref(v___y_2342_);
lean_inc_ref(v___x_2346_);
v___x_2347_ = lean_infer_type(v___x_2346_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2349_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
lean_inc(v_a_2348_);
lean_dec_ref_known(v___x_2347_, 1);
v___x_2349_ = l_Lean_Meta_instantiateForall(v_a_2348_, v___x_2300_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2352_ = lean_unsigned_to_nat(3u);
v___x_2353_ = l_Lean_Expr_isAppOfArity(v_a_2350_, v___x_2351_, v___x_2352_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
lean_dec(v_a_2350_);
lean_dec_ref(v___x_2346_);
lean_dec_ref(v___x_2300_);
lean_dec(v_snd_2286_);
lean_dec(v_cls_2275_);
v___x_2354_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2355_ = l_Lean_MessageData_ofName(v___x_2294_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set_tag(v___x_2288_, 7);
lean_ctor_set(v___x_2288_, 1, v___x_2355_);
lean_ctor_set(v___x_2288_, 0, v___x_2354_);
v___x_2357_ = v___x_2288_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2358_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2357_);
lean_ctor_set(v___x_2359_, 1, v___x_2358_);
v___x_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2360_, 0, v_mvarId_2273_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2361_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v___x_2362_;
}
}
else
{
lean_object* v_toCold_2364_; lean_object* v_options_2365_; lean_object* v_inheritedTraceOptions_2366_; uint8_t v_hasTrace_2367_; lean_object* v___x_2368_; lean_object* v_nargs_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec(v___x_2294_);
v_toCold_2364_ = lean_ctor_get(v___y_2344_, 0);
v_options_2365_ = lean_ctor_get(v_toCold_2364_, 2);
v_inheritedTraceOptions_2366_ = lean_ctor_get(v_toCold_2364_, 11);
v_hasTrace_2367_ = lean_ctor_get_uint8(v_options_2365_, sizeof(void*)*1);
v___x_2368_ = l_Lean_Expr_appArg_x21(v_a_2350_);
lean_dec(v_a_2350_);
v_nargs_2369_ = l_Lean_Expr_getAppNumArgs(v___x_2368_);
lean_inc(v_nargs_2369_);
v___x_2370_ = lean_mk_array(v_nargs_2369_, v_dummy_2295_);
v___x_2371_ = lean_nat_sub(v_nargs_2369_, v___x_2298_);
lean_dec(v_nargs_2369_);
lean_inc_ref(v___x_2368_);
v___x_2372_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2368_, v___x_2370_, v___x_2371_);
v___x_2373_ = lean_array_get_size(v___x_2372_);
v___x_2374_ = lean_nat_sub(v___x_2373_, v___x_2298_);
v___x_2375_ = lean_array_get(v___x_2274_, v___x_2372_, v___x_2374_);
lean_dec(v___x_2374_);
lean_dec_ref(v___x_2372_);
if (v_hasTrace_2367_ == 0)
{
lean_del_object(v___x_2288_);
lean_dec(v_cls_2275_);
v___y_2302_ = v___x_2375_;
v___y_2303_ = v___x_2346_;
v___y_2304_ = v___x_2368_;
v___y_2305_ = v___x_2353_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___y_2343_;
v___y_2308_ = v___y_2344_;
v___y_2309_ = v___y_2345_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2275_);
v___x_2377_ = l_Lean_Name_append(v___x_2376_, v_cls_2275_);
v___x_2378_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2366_, v_options_2365_, v___x_2377_);
lean_dec(v___x_2377_);
if (v___x_2378_ == 0)
{
lean_del_object(v___x_2288_);
lean_dec(v_cls_2275_);
v___y_2302_ = v___x_2375_;
v___y_2303_ = v___x_2346_;
v___y_2304_ = v___x_2368_;
v___y_2305_ = v___x_2353_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___y_2343_;
v___y_2308_ = v___y_2344_;
v___y_2309_ = v___y_2345_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2379_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2380_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2375_);
v___x_2381_ = l_Lean_inlineExpr(v___x_2375_, v___x_2380_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set_tag(v___x_2288_, 7);
lean_ctor_set(v___x_2288_, 1, v___x_2381_);
lean_ctor_set(v___x_2288_, 0, v___x_2379_);
v___x_2383_ = v___x_2288_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2384_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2383_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
lean_inc_ref(v___x_2368_);
v___x_2386_ = l_Lean_indentExpr(v___x_2368_);
v___x_2387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2385_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2275_, v___x_2387_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_dec_ref_known(v___x_2388_, 1);
v___y_2302_ = v___x_2375_;
v___y_2303_ = v___x_2346_;
v___y_2304_ = v___x_2368_;
v___y_2305_ = v___x_2353_;
v___y_2306_ = v___y_2342_;
v___y_2307_ = v___y_2343_;
v___y_2308_ = v___y_2344_;
v___y_2309_ = v___y_2345_;
goto v___jp_2301_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v___x_2375_);
lean_dec_ref(v___x_2368_);
lean_dec_ref(v___x_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___x_2300_);
lean_dec(v_snd_2286_);
lean_dec(v_mvarId_2273_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
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
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v___x_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___x_2300_);
lean_dec(v___x_2294_);
lean_del_object(v___x_2288_);
lean_dec(v_snd_2286_);
lean_dec(v_cls_2275_);
lean_dec(v_mvarId_2273_);
v_a_2398_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2349_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2349_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v___x_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec_ref(v___x_2300_);
lean_dec(v___x_2294_);
lean_del_object(v___x_2288_);
lean_dec(v_snd_2286_);
lean_dec(v_cls_2275_);
lean_dec(v_mvarId_2273_);
v_a_2406_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2347_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2347_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
v_resetjp_2417_:
{
uint8_t v___x_2420_; 
v___x_2420_ = lean_unbox(v_a_2416_);
lean_dec(v_a_2416_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
lean_dec_ref(v___x_2300_);
lean_dec(v___x_2292_);
lean_del_object(v___x_2288_);
lean_dec(v_snd_2286_);
lean_dec(v_cls_2275_);
v___x_2421_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2422_ = l_Lean_MessageData_ofName(v___x_2294_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2425_, 0, v___x_2423_);
lean_ctor_set(v___x_2425_, 1, v___x_2424_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set_tag(v___x_2418_, 1);
lean_ctor_set(v___x_2418_, 0, v_mvarId_2273_);
v___x_2427_ = v___x_2418_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_mvarId_2273_);
v___x_2427_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
v___x_2428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2425_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2428_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
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
else
{
lean_del_object(v___x_2418_);
v___y_2342_ = v___y_2276_;
v___y_2343_ = v___y_2277_;
v___y_2344_ = v___y_2278_;
v___y_2345_ = v___y_2279_;
goto v___jp_2341_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v_cls_2275_);
lean_dec(v_mvarId_2273_);
v_a_2441_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2283_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2283_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v_cls_2275_);
lean_dec(v_mvarId_2273_);
v_a_2449_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2281_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2281_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2273_ = stack[0].m_obj;
lean_object* v___x_2274_ = stack[1].m_obj;
lean_object* v_cls_2275_ = stack[2].m_obj;
lean_object* v___y_2276_ = stack[3].m_obj;
lean_object* v___y_2277_ = stack[4].m_obj;
lean_object* v___y_2278_ = stack[5].m_obj;
lean_object* v___y_2279_ = stack[6].m_obj;
lean_object* v_res_2457_;
v_res_2457_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2273_, v___x_2274_, v_cls_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
stack->m_obj
 = v_res_2457_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2458_, lean_object* v___x_2459_, lean_object* v_cls_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2458_, v___x_2459_, v_cls_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec_ref(v___x_2459_);
return v_res_2466_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2469_ = l_Lean_stringToMessageData(v___x_2468_);
return v___x_2469_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2470_, lean_object* v_x_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2478_, 0, v_mvarId_2470_);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2470_ = stack[0].m_obj;
lean_object* v_x_2471_ = stack[1].m_obj;
lean_object* v___y_2472_ = stack[2].m_obj;
lean_object* v___y_2473_ = stack[3].m_obj;
lean_object* v___y_2474_ = stack[4].m_obj;
lean_object* v___y_2475_ = stack[5].m_obj;
lean_object* v_res_2481_;
v_res_2481_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2470_, v_x_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
stack->m_obj
 = v_res_2481_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2482_, lean_object* v_x_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2482_, v_x_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_x_2483_);
return v_res_2489_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2490_, lean_object* v_mvarId_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_toCold_2497_; lean_object* v_options_2498_; lean_object* v_inheritedTraceOptions_2499_; uint8_t v_hasTrace_2500_; lean_object* v___x_2501_; lean_object* v_cls_2502_; lean_object* v___f_2503_; 
v_toCold_2497_ = lean_ctor_get(v_a_2494_, 0);
v_options_2498_ = lean_ctor_get(v_toCold_2497_, 2);
v_inheritedTraceOptions_2499_ = lean_ctor_get(v_toCold_2497_, 11);
v_hasTrace_2500_ = lean_ctor_get_uint8(v_options_2498_, sizeof(void*)*1);
v___x_2501_ = l_Lean_instInhabitedExpr;
v_cls_2502_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2491_);
v___f_2503_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2503_, 0, v_mvarId_2491_);
lean_closure_set(v___f_2503_, 1, v___x_2501_);
lean_closure_set(v___f_2503_, 2, v_cls_2502_);
if (v_hasTrace_2500_ == 0)
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2491_, v___f_2503_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2490_, v_a_2505_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2506_;
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec(v_declName_2490_);
v_a_2507_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2504_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2504_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_object* v___f_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v_a_2522_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v_a_2537_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v_a_2542_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v_a_2554_; 
lean_inc(v_mvarId_2491_);
v___f_2515_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2515_, 0, v_mvarId_2491_);
v___x_2516_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2517_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2499_, v_options_2498_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = l_Lean_trace_profiler;
v___x_2590_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2498_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
lean_dec_ref(v___f_2515_);
v___x_2591_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2491_, v___f_2503_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2490_, v_a_2592_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2593_;
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_declName_2490_);
v_a_2594_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2591_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2591_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
else
{
goto v___jp_2556_;
}
}
else
{
goto v___jp_2556_;
}
v___jp_2519_:
{
lean_object* v___x_2523_; double v___x_2524_; double v___x_2525_; double v___x_2526_; double v___x_2527_; double v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2523_ = lean_io_mono_nanos_now();
v___x_2524_ = lean_float_of_nat(v___y_2520_);
v___x_2525_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2526_ = lean_float_div(v___x_2524_, v___x_2525_);
v___x_2527_ = lean_float_of_nat(v___x_2523_);
v___x_2528_ = lean_float_div(v___x_2527_, v___x_2525_);
v___x_2529_ = lean_box_float(v___x_2526_);
v___x_2530_ = lean_box_float(v___x_2528_);
v___x_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v_a_2522_);
lean_ctor_set(v___x_2532_, 1, v___x_2531_);
v___x_2533_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2502_, v_hasTrace_2500_, v___x_2516_, v_options_2498_, v___x_2518_, v___y_2521_, v___f_2515_, v___x_2532_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2533_;
}
v___jp_2534_:
{
lean_object* v___x_2538_; 
v___x_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_a_2537_);
v___y_2520_ = v___y_2535_;
v___y_2521_ = v___y_2536_;
v_a_2522_ = v___x_2538_;
goto v___jp_2519_;
}
v___jp_2539_:
{
lean_object* v___x_2543_; double v___x_2544_; double v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2543_ = lean_io_get_num_heartbeats();
v___x_2544_ = lean_float_of_nat(v___y_2540_);
v___x_2545_ = lean_float_of_nat(v___x_2543_);
v___x_2546_ = lean_box_float(v___x_2544_);
v___x_2547_ = lean_box_float(v___x_2545_);
v___x_2548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2546_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_a_2542_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2502_, v_hasTrace_2500_, v___x_2516_, v_options_2498_, v___x_2518_, v___y_2541_, v___f_2515_, v___x_2549_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2550_;
}
v___jp_2551_:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_a_2554_);
v___y_2540_ = v___y_2552_;
v___y_2541_ = v___y_2553_;
v_a_2542_ = v___x_2555_;
goto v___jp_2539_;
}
v___jp_2556_:
{
lean_object* v___x_2557_; lean_object* v_a_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2557_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2495_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2560_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2498_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_io_mono_nanos_now();
v___x_2562_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2491_, v___f_2503_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2564_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2490_, v_a_2563_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 1);
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
v___y_2520_ = v___x_2561_;
v___y_2521_ = v_a_2558_;
v_a_2522_ = v___x_2570_;
goto v___jp_2519_;
}
}
}
else
{
lean_object* v_a_2573_; 
v_a_2573_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2564_, 1);
v___y_2535_ = v___x_2561_;
v___y_2536_ = v_a_2558_;
v_a_2537_ = v_a_2573_;
goto v___jp_2534_;
}
}
else
{
lean_object* v_a_2574_; 
lean_dec(v_declName_2490_);
v_a_2574_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2562_, 1);
v___y_2535_ = v___x_2561_;
v___y_2536_ = v_a_2558_;
v_a_2537_ = v_a_2574_;
goto v___jp_2534_;
}
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2575_ = lean_io_get_num_heartbeats();
v___x_2576_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2491_, v___f_2503_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2490_, v_a_2577_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set_tag(v___x_2581_, 1);
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
v___y_2540_ = v___x_2575_;
v___y_2541_ = v_a_2558_;
v_a_2542_ = v___x_2584_;
goto v___jp_2539_;
}
}
}
else
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2578_, 1);
v___y_2552_ = v___x_2575_;
v___y_2553_ = v_a_2558_;
v_a_2554_ = v_a_2587_;
goto v___jp_2551_;
}
}
else
{
lean_object* v_a_2588_; 
lean_dec(v_declName_2490_);
v_a_2588_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2576_, 1);
v___y_2552_ = v___x_2575_;
v___y_2553_ = v_a_2558_;
v_a_2554_ = v_a_2588_;
goto v___jp_2551_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2490_ = stack[0].m_obj;
lean_object* v_mvarId_2491_ = stack[1].m_obj;
lean_object* v_a_2492_ = stack[2].m_obj;
lean_object* v_a_2493_ = stack[3].m_obj;
lean_object* v_a_2494_ = stack[4].m_obj;
lean_object* v_a_2495_ = stack[5].m_obj;
lean_object* v_res_2602_;
v_res_2602_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2490_, v_mvarId_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
stack->m_obj
 = v_res_2602_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2603_, lean_object* v_mvarId_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2603_, v_mvarId_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_);
lean_dec(v_a_2608_);
lean_dec_ref(v_a_2607_);
lean_dec(v_a_2606_);
lean_dec_ref(v_a_2605_);
return v_res_2610_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2611_, lean_object* v___y_2612_){
_start:
{
uint8_t v___x_2614_; 
v___x_2614_ = l_Lean_Expr_hasMVar(v_e_2611_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2615_, 0, v_e_2611_);
return v___x_2615_;
}
else
{
lean_object* v___x_2616_; lean_object* v_mctx_2617_; lean_object* v___x_2618_; lean_object* v_fst_2619_; lean_object* v_snd_2620_; lean_object* v___x_2621_; lean_object* v_cache_2622_; lean_object* v_zetaDeltaFVarIds_2623_; lean_object* v_postponed_2624_; lean_object* v_diag_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2634_; 
v___x_2616_ = lean_st_ref_get(v___y_2612_);
v_mctx_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc_ref(v_mctx_2617_);
lean_dec(v___x_2616_);
v___x_2618_ = l_Lean_instantiateMVarsCore(v_mctx_2617_, v_e_2611_);
v_fst_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_fst_2619_);
v_snd_2620_ = lean_ctor_get(v___x_2618_, 1);
lean_inc(v_snd_2620_);
lean_dec_ref(v___x_2618_);
v___x_2621_ = lean_st_ref_take(v___y_2612_);
v_cache_2622_ = lean_ctor_get(v___x_2621_, 1);
v_zetaDeltaFVarIds_2623_ = lean_ctor_get(v___x_2621_, 2);
v_postponed_2624_ = lean_ctor_get(v___x_2621_, 3);
v_diag_2625_ = lean_ctor_get(v___x_2621_, 4);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; 
v_unused_2635_ = lean_ctor_get(v___x_2621_, 0);
lean_dec(v_unused_2635_);
v___x_2627_ = v___x_2621_;
v_isShared_2628_ = v_isSharedCheck_2634_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_diag_2625_);
lean_inc(v_postponed_2624_);
lean_inc(v_zetaDeltaFVarIds_2623_);
lean_inc(v_cache_2622_);
lean_dec(v___x_2621_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2634_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 0, v_snd_2620_);
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_snd_2620_);
lean_ctor_set(v_reuseFailAlloc_2633_, 1, v_cache_2622_);
lean_ctor_set(v_reuseFailAlloc_2633_, 2, v_zetaDeltaFVarIds_2623_);
lean_ctor_set(v_reuseFailAlloc_2633_, 3, v_postponed_2624_);
lean_ctor_set(v_reuseFailAlloc_2633_, 4, v_diag_2625_);
v___x_2630_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_st_ref_put(v___y_2612_, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_fst_2619_);
return v___x_2632_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2611_ = stack[0].m_obj;
lean_object* v___y_2612_ = stack[1].m_obj;
lean_object* v_res_2636_;
v_res_2636_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2611_, v___y_2612_);
stack->m_obj
 = v_res_2636_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2637_, v___y_2638_);
lean_dec(v___y_2638_);
return v_res_2640_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2641_, v___y_2643_);
return v___x_2647_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2641_ = stack[0].m_obj;
lean_object* v___y_2642_ = stack[1].m_obj;
lean_object* v___y_2643_ = stack[2].m_obj;
lean_object* v___y_2644_ = stack[3].m_obj;
lean_object* v___y_2645_ = stack[4].m_obj;
lean_object* v_res_2648_;
v_res_2648_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
stack->m_obj
 = v_res_2648_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2655_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2656_, uint8_t v_allowLevelAssignments_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2657_, v_k_2656_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2663_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2663_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
v_a_2672_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2663_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2663_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2656_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_2657_ = stack[1].m_num;
lean_object* v___y_2658_ = stack[2].m_obj;
lean_object* v___y_2659_ = stack[3].m_obj;
lean_object* v___y_2660_ = stack[4].m_obj;
lean_object* v___y_2661_ = stack[5].m_obj;
lean_object* v_res_2680_;
v_res_2680_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2656_, v_allowLevelAssignments_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
stack->m_obj
 = v_res_2680_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2681_, lean_object* v_allowLevelAssignments_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2688_; lean_object* v_res_2689_; 
v_allowLevelAssignments_boxed_2688_ = lean_unbox(v_allowLevelAssignments_2682_);
v_res_2689_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2681_, v_allowLevelAssignments_boxed_2688_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2689_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2690_, lean_object* v_k_2691_, uint8_t v_allowLevelAssignments_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2691_, v_allowLevelAssignments_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2691_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_2692_ = stack[2].m_num;
lean_object* v___y_2693_ = stack[3].m_obj;
lean_object* v___y_2694_ = stack[4].m_obj;
lean_object* v___y_2695_ = stack[5].m_obj;
lean_object* v___y_2696_ = stack[6].m_obj;
lean_object* v_res_2699_;
v_res_2699_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_box(0), v_k_2691_, v_allowLevelAssignments_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
stack->m_obj
 = v_res_2699_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2700_, lean_object* v_k_2701_, lean_object* v_allowLevelAssignments_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2708_; lean_object* v_res_2709_; 
v_allowLevelAssignments_boxed_2708_ = lean_unbox(v_allowLevelAssignments_2702_);
v_res_2709_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2700_, v_k_2701_, v_allowLevelAssignments_boxed_2708_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2710_, lean_object* v_e_2711_){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2712_ = l_Lean_indentD(v_e_2711_);
v___x_2713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2710_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
return v___x_2713_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2714_, lean_object* v___x_2715_, lean_object* v_declName_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2714_, v___x_2715_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = l_Lean_Expr_mvarId_x21(v_a_2723_);
v___x_2725_ = l_Lean_MVarId_intros(v___x_2724_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v_snd_2727_; lean_object* v___x_2728_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v_snd_2727_ = lean_ctor_get(v_a_2726_, 1);
lean_inc_n(v_snd_2727_, 2);
lean_dec(v_a_2726_);
v___x_2728_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2727_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; uint8_t v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc(v_a_2729_);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = lean_unbox(v_a_2729_);
lean_dec(v_a_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2727_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2716_, v_a_2732_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v___x_2734_; 
lean_dec_ref_known(v___x_2733_, 1);
v___x_2734_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2723_, v___y_2718_);
return v___x_2734_;
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec(v_a_2723_);
v_a_2735_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2733_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2733_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_a_2723_);
lean_dec(v_declName_2716_);
v_a_2743_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2731_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2731_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v___x_2751_; 
lean_dec(v_snd_2727_);
lean_dec(v_declName_2716_);
v___x_2751_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2723_, v___y_2718_);
return v___x_2751_;
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_snd_2727_);
lean_dec(v_a_2723_);
lean_dec(v_declName_2716_);
v_a_2752_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2728_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2728_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2723_);
lean_dec(v_declName_2716_);
v_a_2760_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2725_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2725_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_dec(v_declName_2716_);
return v___x_2722_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2714_ = stack[0].m_obj;
lean_object* v___x_2715_ = stack[1].m_obj;
lean_object* v_declName_2716_ = stack[2].m_obj;
lean_object* v___y_2717_ = stack[3].m_obj;
lean_object* v___y_2718_ = stack[4].m_obj;
lean_object* v___y_2719_ = stack[5].m_obj;
lean_object* v___y_2720_ = stack[6].m_obj;
lean_object* v_res_2768_;
v_res_2768_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2714_, v___x_2715_, v_declName_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
stack->m_obj
 = v_res_2768_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2769_, lean_object* v___x_2770_, lean_object* v_declName_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2769_, v___x_2770_, v_declName_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
return v_res_2777_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2780_ = l_Lean_stringToMessageData(v___x_2779_);
return v___x_2780_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2781_, lean_object* v_x_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2788_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2789_ = l_Lean_indentExpr(v_type_2781_);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2790_);
return v___x_2791_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2781_ = stack[0].m_obj;
lean_object* v_x_2782_ = stack[1].m_obj;
lean_object* v___y_2783_ = stack[2].m_obj;
lean_object* v___y_2784_ = stack[3].m_obj;
lean_object* v___y_2785_ = stack[4].m_obj;
lean_object* v___y_2786_ = stack[5].m_obj;
lean_object* v_res_2792_;
v_res_2792_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2781_, v_x_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
stack->m_obj
 = v_res_2792_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2793_, lean_object* v_x_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2793_, v_x_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v_x_2794_);
return v_res_2800_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2801_){
_start:
{
if (lean_obj_tag(v_e_2801_) == 0)
{
uint8_t v___x_2802_; 
v___x_2802_ = 2;
return v___x_2802_;
}
else
{
lean_object* v_a_2803_; uint8_t v___x_2804_; 
v_a_2803_ = lean_ctor_get(v_e_2801_, 0);
v___x_2804_ = l_Lean_Expr_hasSyntheticSorry(v_a_2803_);
if (v___x_2804_ == 0)
{
uint8_t v___x_2805_; 
v___x_2805_ = 0;
return v___x_2805_;
}
else
{
uint8_t v___x_2806_; 
v___x_2806_ = 1;
return v___x_2806_;
}
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2801_ = stack[0].m_obj;
uint8_t v_res_2807_;
v_res_2807_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2801_);
stack->m_num = v_res_2807_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2808_){
_start:
{
uint8_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2808_);
lean_dec_ref(v_e_2808_);
v_r_2810_ = lean_box(v_res_2809_);
return v_r_2810_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2811_, uint8_t v_collapsed_2812_, lean_object* v_tag_2813_, lean_object* v_opts_2814_, uint8_t v_clsEnabled_2815_, lean_object* v_oldTraces_2816_, lean_object* v_msg_2817_, lean_object* v_resStartStop_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_fst_2824_; lean_object* v_snd_2825_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v_data_2829_; lean_object* v_fst_2840_; lean_object* v_snd_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; lean_object* v___y_2845_; lean_object* v_a_2846_; uint8_t v___y_2861_; double v___y_2893_; 
v_fst_2824_ = lean_ctor_get(v_resStartStop_2818_, 0);
lean_inc(v_fst_2824_);
v_snd_2825_ = lean_ctor_get(v_resStartStop_2818_, 1);
lean_inc(v_snd_2825_);
lean_dec_ref(v_resStartStop_2818_);
v_fst_2840_ = lean_ctor_get(v_snd_2825_, 0);
lean_inc(v_fst_2840_);
v_snd_2841_ = lean_ctor_get(v_snd_2825_, 1);
lean_inc(v_snd_2841_);
lean_dec(v_snd_2825_);
v___x_2842_ = l_Lean_trace_profiler;
v___x_2843_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2814_, v___x_2842_);
if (v___x_2843_ == 0)
{
v___y_2861_ = v___x_2843_;
goto v___jp_2860_;
}
else
{
lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2898_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2899_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2814_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; double v___x_2902_; double v___x_2903_; double v___x_2904_; 
v___x_2900_ = l_Lean_trace_profiler_threshold;
v___x_2901_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2814_, v___x_2900_);
v___x_2902_ = lean_float_of_nat(v___x_2901_);
v___x_2903_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_2904_ = lean_float_div(v___x_2902_, v___x_2903_);
v___y_2893_ = v___x_2904_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; double v___x_2907_; 
v___x_2905_ = l_Lean_trace_profiler_threshold;
v___x_2906_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2814_, v___x_2905_);
v___x_2907_ = lean_float_of_nat(v___x_2906_);
v___y_2893_ = v___x_2907_;
goto v___jp_2892_;
}
}
v___jp_2826_:
{
lean_object* v___x_2830_; 
lean_inc(v___y_2828_);
v___x_2830_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_2816_, v_data_2829_, v___y_2828_, v___y_2827_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v___x_2831_; 
lean_dec_ref_known(v___x_2830_, 1);
v___x_2831_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2824_);
return v___x_2831_;
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_fst_2824_);
v_a_2832_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2830_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2830_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
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
v___jp_2844_:
{
uint8_t v_result_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; double v___x_2850_; lean_object* v_data_2851_; 
v_result_2847_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2824_);
v___x_2848_ = lean_box(v_result_2847_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
v___x_2850_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2813_);
lean_inc_ref(v___x_2849_);
lean_inc(v_cls_2811_);
v_data_2851_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2851_, 0, v_cls_2811_);
lean_ctor_set(v_data_2851_, 1, v___x_2849_);
lean_ctor_set(v_data_2851_, 2, v_tag_2813_);
lean_ctor_set_float(v_data_2851_, sizeof(void*)*3, v___x_2850_);
lean_ctor_set_float(v_data_2851_, sizeof(void*)*3 + 8, v___x_2850_);
lean_ctor_set_uint8(v_data_2851_, sizeof(void*)*3 + 16, v_collapsed_2812_);
if (v___x_2843_ == 0)
{
lean_dec_ref_known(v___x_2849_, 1);
lean_dec(v_snd_2841_);
lean_dec(v_fst_2840_);
lean_dec_ref(v_tag_2813_);
lean_dec(v_cls_2811_);
v___y_2827_ = v_a_2846_;
v___y_2828_ = v___y_2845_;
v_data_2829_ = v_data_2851_;
goto v___jp_2826_;
}
else
{
lean_object* v_data_2852_; double v___x_2853_; double v___x_2854_; 
lean_dec_ref_known(v_data_2851_, 3);
v_data_2852_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2852_, 0, v_cls_2811_);
lean_ctor_set(v_data_2852_, 1, v___x_2849_);
lean_ctor_set(v_data_2852_, 2, v_tag_2813_);
v___x_2853_ = lean_unbox_float(v_fst_2840_);
lean_dec(v_fst_2840_);
lean_ctor_set_float(v_data_2852_, sizeof(void*)*3, v___x_2853_);
v___x_2854_ = lean_unbox_float(v_snd_2841_);
lean_dec(v_snd_2841_);
lean_ctor_set_float(v_data_2852_, sizeof(void*)*3 + 8, v___x_2854_);
lean_ctor_set_uint8(v_data_2852_, sizeof(void*)*3 + 16, v_collapsed_2812_);
v___y_2827_ = v_a_2846_;
v___y_2828_ = v___y_2845_;
v_data_2829_ = v_data_2852_;
goto v___jp_2826_;
}
}
v___jp_2855_:
{
lean_object* v_ref_2856_; lean_object* v___x_2857_; 
v_ref_2856_ = lean_ctor_get(v___y_2821_, 2);
lean_inc(v___y_2822_);
lean_inc_ref(v___y_2821_);
lean_inc(v___y_2820_);
lean_inc_ref(v___y_2819_);
lean_inc(v_fst_2824_);
v___x_2857_ = lean_apply_6(v_msg_2817_, v_fst_2824_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_, lean_box(0));
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___y_2845_ = v_ref_2856_;
v_a_2846_ = v_a_2858_;
goto v___jp_2844_;
}
else
{
lean_object* v___x_2859_; 
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_2845_ = v_ref_2856_;
v_a_2846_ = v___x_2859_;
goto v___jp_2844_;
}
}
v___jp_2860_:
{
if (v_clsEnabled_2815_ == 0)
{
if (v___y_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v_traceState_2863_; lean_object* v_env_2864_; lean_object* v_nextMacroScope_2865_; lean_object* v_ngen_2866_; lean_object* v_auxDeclNGen_2867_; lean_object* v_cache_2868_; lean_object* v_recordedDeps_2869_; lean_object* v_messages_2870_; lean_object* v_infoState_2871_; lean_object* v_snapshotTasks_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_snd_2841_);
lean_dec(v_fst_2840_);
lean_dec_ref(v_msg_2817_);
lean_dec_ref(v_tag_2813_);
lean_dec(v_cls_2811_);
v___x_2862_ = lean_st_ref_take(v___y_2822_);
v_traceState_2863_ = lean_ctor_get(v___x_2862_, 4);
v_env_2864_ = lean_ctor_get(v___x_2862_, 0);
v_nextMacroScope_2865_ = lean_ctor_get(v___x_2862_, 1);
v_ngen_2866_ = lean_ctor_get(v___x_2862_, 2);
v_auxDeclNGen_2867_ = lean_ctor_get(v___x_2862_, 3);
v_cache_2868_ = lean_ctor_get(v___x_2862_, 5);
v_recordedDeps_2869_ = lean_ctor_get(v___x_2862_, 6);
v_messages_2870_ = lean_ctor_get(v___x_2862_, 7);
v_infoState_2871_ = lean_ctor_get(v___x_2862_, 8);
v_snapshotTasks_2872_ = lean_ctor_get(v___x_2862_, 9);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2874_ = v___x_2862_;
v_isShared_2875_ = v_isSharedCheck_2891_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_snapshotTasks_2872_);
lean_inc(v_infoState_2871_);
lean_inc(v_messages_2870_);
lean_inc(v_recordedDeps_2869_);
lean_inc(v_cache_2868_);
lean_inc(v_traceState_2863_);
lean_inc(v_auxDeclNGen_2867_);
lean_inc(v_ngen_2866_);
lean_inc(v_nextMacroScope_2865_);
lean_inc(v_env_2864_);
lean_dec(v___x_2862_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2891_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
uint64_t v_tid_2876_; lean_object* v_traces_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2890_; 
v_tid_2876_ = lean_ctor_get_uint64(v_traceState_2863_, sizeof(void*)*1);
v_traces_2877_ = lean_ctor_get(v_traceState_2863_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v_traceState_2863_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2879_ = v_traceState_2863_;
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_traces_2877_);
lean_dec(v_traceState_2863_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2890_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2816_, v_traces_2877_);
lean_dec_ref(v_traces_2877_);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 0, v___x_2881_);
v___x_2883_ = v___x_2879_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2881_);
lean_ctor_set_uint64(v_reuseFailAlloc_2889_, sizeof(void*)*1, v_tid_2876_);
v___x_2883_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2885_; 
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 4, v___x_2883_);
v___x_2885_ = v___x_2874_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_env_2864_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_nextMacroScope_2865_);
lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_ngen_2866_);
lean_ctor_set(v_reuseFailAlloc_2888_, 3, v_auxDeclNGen_2867_);
lean_ctor_set(v_reuseFailAlloc_2888_, 4, v___x_2883_);
lean_ctor_set(v_reuseFailAlloc_2888_, 5, v_cache_2868_);
lean_ctor_set(v_reuseFailAlloc_2888_, 6, v_recordedDeps_2869_);
lean_ctor_set(v_reuseFailAlloc_2888_, 7, v_messages_2870_);
lean_ctor_set(v_reuseFailAlloc_2888_, 8, v_infoState_2871_);
lean_ctor_set(v_reuseFailAlloc_2888_, 9, v_snapshotTasks_2872_);
v___x_2885_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = lean_st_ref_put(v___y_2822_, v___x_2885_);
v___x_2887_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2824_);
return v___x_2887_;
}
}
}
}
}
else
{
goto v___jp_2855_;
}
}
else
{
goto v___jp_2855_;
}
}
v___jp_2892_:
{
double v___x_2894_; double v___x_2895_; double v___x_2896_; uint8_t v___x_2897_; 
v___x_2894_ = lean_unbox_float(v_snd_2841_);
v___x_2895_ = lean_unbox_float(v_fst_2840_);
v___x_2896_ = lean_float_sub(v___x_2894_, v___x_2895_);
v___x_2897_ = lean_float_decLt(v___y_2893_, v___x_2896_);
v___y_2861_ = v___x_2897_;
goto v___jp_2860_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2811_ = stack[0].m_obj;
uint8_t v_collapsed_2812_ = stack[1].m_num;
lean_object* v_tag_2813_ = stack[2].m_obj;
lean_object* v_opts_2814_ = stack[3].m_obj;
uint8_t v_clsEnabled_2815_ = stack[4].m_num;
lean_object* v_oldTraces_2816_ = stack[5].m_obj;
lean_object* v_msg_2817_ = stack[6].m_obj;
lean_object* v_resStartStop_2818_ = stack[7].m_obj;
lean_object* v___y_2819_ = stack[8].m_obj;
lean_object* v___y_2820_ = stack[9].m_obj;
lean_object* v___y_2821_ = stack[10].m_obj;
lean_object* v___y_2822_ = stack[11].m_obj;
lean_object* v_res_2908_;
v_res_2908_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2811_, v_collapsed_2812_, v_tag_2813_, v_opts_2814_, v_clsEnabled_2815_, v_oldTraces_2816_, v_msg_2817_, v_resStartStop_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
stack->m_obj
 = v_res_2908_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2909_, lean_object* v_collapsed_2910_, lean_object* v_tag_2911_, lean_object* v_opts_2912_, lean_object* v_clsEnabled_2913_, lean_object* v_oldTraces_2914_, lean_object* v_msg_2915_, lean_object* v_resStartStop_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
uint8_t v_collapsed_boxed_2922_; uint8_t v_clsEnabled_boxed_2923_; lean_object* v_res_2924_; 
v_collapsed_boxed_2922_ = lean_unbox(v_collapsed_2910_);
v_clsEnabled_boxed_2923_ = lean_unbox(v_clsEnabled_2913_);
v_res_2924_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2909_, v_collapsed_boxed_2922_, v_tag_2911_, v_opts_2912_, v_clsEnabled_boxed_2923_, v_oldTraces_2914_, v_msg_2915_, v_resStartStop_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v_opts_2912_);
return v_res_2924_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2927_ = l_Lean_stringToMessageData(v___x_2926_);
return v___x_2927_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2929_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2930_ = l_Lean_stringToMessageData(v___x_2929_);
return v___x_2930_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2931_, lean_object* v_type_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_toCold_2938_; lean_object* v_options_2939_; lean_object* v_inheritedTraceOptions_2940_; uint8_t v_hasTrace_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___f_2948_; lean_object* v___x_2949_; lean_object* v___f_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_toCold_2938_ = lean_ctor_get(v_a_2935_, 0);
v_options_2939_ = lean_ctor_get(v_toCold_2938_, 2);
v_inheritedTraceOptions_2940_ = lean_ctor_get(v_toCold_2938_, 11);
v_hasTrace_2941_ = lean_ctor_get_uint8(v_options_2939_, sizeof(void*)*1);
v___x_2942_ = 0;
lean_inc(v_declName_2931_);
v___x_2943_ = l_Lean_MessageData_ofConstName(v_declName_2931_, v___x_2942_);
v___x_2944_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_2945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
lean_ctor_set(v___x_2945_, 1, v___x_2943_);
v___x_2946_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_2947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2945_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___f_2948_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_2948_, 0, v___x_2947_);
v___x_2949_ = lean_box(0);
lean_inc_ref(v_type_2932_);
v___f_2950_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2950_, 0, v_type_2932_);
lean_closure_set(v___f_2950_, 1, v___x_2949_);
lean_closure_set(v___f_2950_, 2, v_declName_2931_);
v___x_2951_ = lean_box(v___x_2942_);
v___x_2952_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2952_, 0, lean_box(0));
lean_closure_set(v___x_2952_, 1, v___f_2950_);
lean_closure_set(v___x_2952_, 2, v___x_2951_);
if (v_hasTrace_2941_ == 0)
{
lean_object* v___x_2953_; 
lean_dec_ref(v_type_2932_);
v___x_2953_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2952_, v___f_2948_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
else
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
v_a_2962_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2953_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2953_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v___f_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v_a_2978_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v_a_2993_; 
v___f_2970_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2970_, 0, v_type_2932_);
v___x_2971_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_2972_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2973_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2940_, v_options_2939_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = l_Lean_trace_profiler;
v___x_3044_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2939_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; 
lean_dec_ref(v___f_2970_);
v___x_3045_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2952_, v___f_2948_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3045_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
v_a_3054_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3045_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3045_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
else
{
goto v___jp_3002_;
}
}
else
{
goto v___jp_3002_;
}
v___jp_2975_:
{
lean_object* v___x_2979_; double v___x_2980_; double v___x_2981_; double v___x_2982_; double v___x_2983_; double v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2979_ = lean_io_mono_nanos_now();
v___x_2980_ = lean_float_of_nat(v___y_2976_);
v___x_2981_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2982_ = lean_float_div(v___x_2980_, v___x_2981_);
v___x_2983_ = lean_float_of_nat(v___x_2979_);
v___x_2984_ = lean_float_div(v___x_2983_, v___x_2981_);
v___x_2985_ = lean_box_float(v___x_2982_);
v___x_2986_ = lean_box_float(v___x_2984_);
v___x_2987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2985_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_a_2978_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2971_, v_hasTrace_2941_, v___x_2972_, v_options_2939_, v___x_2974_, v___y_2977_, v___f_2970_, v___x_2988_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
return v___x_2989_;
}
v___jp_2990_:
{
lean_object* v___x_2994_; double v___x_2995_; double v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_2994_ = lean_io_get_num_heartbeats();
v___x_2995_ = lean_float_of_nat(v___y_2992_);
v___x_2996_ = lean_float_of_nat(v___x_2994_);
v___x_2997_ = lean_box_float(v___x_2995_);
v___x_2998_ = lean_box_float(v___x_2996_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2997_);
lean_ctor_set(v___x_2999_, 1, v___x_2998_);
v___x_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3000_, 0, v_a_2993_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2971_, v_hasTrace_2941_, v___x_2972_, v_options_2939_, v___x_2974_, v___y_2991_, v___f_2970_, v___x_3000_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
return v___x_3001_;
}
v___jp_3002_:
{
lean_object* v___x_3003_; lean_object* v_a_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v___x_3003_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2936_);
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3006_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2939_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_io_mono_nanos_now();
v___x_3008_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2952_, v___f_2948_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 1);
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
v___y_2976_ = v___x_3007_;
v___y_2977_ = v_a_3004_;
v_a_2978_ = v___x_3014_;
goto v___jp_2975_;
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
v_a_3017_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3008_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3008_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 0);
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
v___y_2976_ = v___x_3007_;
v___y_2977_ = v_a_3004_;
v_a_2978_ = v___x_3022_;
goto v___jp_2975_;
}
}
}
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = lean_io_get_num_heartbeats();
v___x_3026_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2952_, v___f_2948_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3026_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
lean_ctor_set_tag(v___x_3029_, 1);
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
v___y_2991_ = v_a_3004_;
v___y_2992_ = v___x_3025_;
v_a_2993_ = v___x_3032_;
goto v___jp_2990_;
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
v_a_3035_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3026_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3026_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 0);
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
v___y_2991_ = v_a_3004_;
v___y_2992_ = v___x_3025_;
v_a_2993_ = v___x_3040_;
goto v___jp_2990_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2931_ = stack[0].m_obj;
lean_object* v_type_2932_ = stack[1].m_obj;
lean_object* v_a_2933_ = stack[2].m_obj;
lean_object* v_a_2934_ = stack[3].m_obj;
lean_object* v_a_2935_ = stack[4].m_obj;
lean_object* v_a_2936_ = stack[5].m_obj;
lean_object* v_res_3062_;
v_res_3062_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_2931_, v_type_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
stack->m_obj
 = v_res_3062_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3063_, lean_object* v_type_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3063_, v_type_3064_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec_ref(v_a_3065_);
return v_res_3070_;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_3071_, lean_object* v_n_3072_, lean_object* v_x_3073_){
_start:
{
uint8_t v___x_3074_; 
v___x_3074_ = l_Lean_Environment_hasExposedBody(v_env_3071_, v_n_3072_);
return v___x_3074_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_env_3071_ = stack[0].m_obj;
lean_object* v_n_3072_ = stack[1].m_obj;
lean_object* v_x_3073_ = stack[2].m_obj;
uint8_t v_res_3075_;
v_res_3075_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(v_env_3071_, v_n_3072_, v_x_3073_);
stack->m_num = v_res_3075_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_env_3076_, lean_object* v_n_3077_, lean_object* v_x_3078_){
_start:
{
uint8_t v_res_3079_; lean_object* v_r_3080_; 
v_res_3079_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(v_env_3076_, v_n_3077_, v_x_3078_);
lean_dec_ref(v_x_3078_);
v_r_3080_ = lean_box(v_res_3079_);
return v_r_3080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3081_, lean_object* v_x_3082_){
_start:
{
if (lean_obj_tag(v_x_3082_) == 0)
{
lean_object* v_k_3083_; lean_object* v_v_3084_; lean_object* v_l_3085_; lean_object* v_r_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v_k_3083_ = lean_ctor_get(v_x_3082_, 1);
v_v_3084_ = lean_ctor_get(v_x_3082_, 2);
v_l_3085_ = lean_ctor_get(v_x_3082_, 3);
v_r_3086_ = lean_ctor_get(v_x_3082_, 4);
v___x_3087_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3081_, v_l_3085_);
lean_inc(v_v_3084_);
lean_inc(v_k_3083_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_k_3083_);
lean_ctor_set(v___x_3088_, 1, v_v_3084_);
v___x_3089_ = lean_array_push(v___x_3087_, v___x_3088_);
v_init_3081_ = v___x_3089_;
v_x_3082_ = v_r_3086_;
goto _start;
}
else
{
return v_init_3081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3091_, lean_object* v_x_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3091_, v_x_3092_);
lean_dec(v_x_3092_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_3096_, lean_object* v_s_3097_){
_start:
{
lean_object* v___f_3098_; lean_object* v___x_3099_; lean_object* v_all_3100_; lean_object* v___x_3101_; lean_object* v_exported_3102_; lean_object* v___x_3103_; 
v___f_3098_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3098_, 0, v_env_3096_);
v___x_3099_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v_all_3100_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_3099_, v_s_3097_);
v___x_3101_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3098_, v_s_3097_);
v_exported_3102_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_3099_, v___x_3101_);
lean_dec(v___x_3101_);
lean_inc_ref(v_exported_3102_);
v___x_3103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3103_, 0, v_exported_3102_);
lean_ctor_set(v___x_3103_, 1, v_exported_3102_);
lean_ctor_set(v___x_3103_, 2, v_all_3100_);
return v___x_3103_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; lean_object* v___x_3120_; 
v___f_3116_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3117_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3118_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3119_ = 1;
v___x_3120_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3117_, v___x_3118_, v___x_3119_, v___f_3116_);
return v___x_3120_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3121_;
v_res_3121_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3121_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_a_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_();
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0(lean_object* v_init_3124_, lean_object* v_t_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3124_, v_t_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3127_, lean_object* v_t_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0(v_init_3127_, v_t_3128_);
lean_dec(v_t_3128_);
return v_res_3129_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3130_);
return v___x_3131_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
return v___x_3133_;
}
}
lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3134_, lean_object* v_declNames_3135_, lean_object* v_recArgPos_3136_, lean_object* v_fixedParamPerms_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v_levelParams_3141_; lean_object* v_declName_3142_; lean_object* v_type_3143_; lean_object* v_value_3144_; lean_object* v___x_3145_; 
v_levelParams_3141_ = lean_ctor_get(v_preDef_3134_, 1);
lean_inc(v_levelParams_3141_);
v_declName_3142_ = lean_ctor_get(v_preDef_3134_, 3);
lean_inc_n(v_declName_3142_, 2);
v_type_3143_ = lean_ctor_get(v_preDef_3134_, 6);
lean_inc_ref(v_type_3143_);
v_value_3144_ = lean_ctor_get(v_preDef_3134_, 7);
lean_inc_ref(v_value_3144_);
lean_dec_ref(v_preDef_3134_);
v___x_3145_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3142_, v_a_3138_, v_a_3139_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3177_; 
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3177_ == 0)
{
lean_object* v_unused_3178_; 
v_unused_3178_ = lean_ctor_get(v___x_3145_, 0);
lean_dec(v_unused_3178_);
v___x_3147_ = v___x_3145_;
v_isShared_3148_ = v_isSharedCheck_3177_;
goto v_resetjp_3146_;
}
else
{
lean_dec(v___x_3145_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3177_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v_env_3150_; lean_object* v_nextMacroScope_3151_; lean_object* v_ngen_3152_; lean_object* v_auxDeclNGen_3153_; lean_object* v_traceState_3154_; lean_object* v_recordedDeps_3155_; lean_object* v_messages_3156_; lean_object* v_infoState_3157_; lean_object* v_snapshotTasks_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3175_; 
v___x_3149_ = lean_st_ref_take(v_a_3139_);
v_env_3150_ = lean_ctor_get(v___x_3149_, 0);
v_nextMacroScope_3151_ = lean_ctor_get(v___x_3149_, 1);
v_ngen_3152_ = lean_ctor_get(v___x_3149_, 2);
v_auxDeclNGen_3153_ = lean_ctor_get(v___x_3149_, 3);
v_traceState_3154_ = lean_ctor_get(v___x_3149_, 4);
v_recordedDeps_3155_ = lean_ctor_get(v___x_3149_, 6);
v_messages_3156_ = lean_ctor_get(v___x_3149_, 7);
v_infoState_3157_ = lean_ctor_get(v___x_3149_, 8);
v_snapshotTasks_3158_ = lean_ctor_get(v___x_3149_, 9);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v___x_3149_, 5);
lean_dec(v_unused_3176_);
v___x_3160_ = v___x_3149_;
v_isShared_3161_ = v_isSharedCheck_3175_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_snapshotTasks_3158_);
lean_inc(v_infoState_3157_);
lean_inc(v_messages_3156_);
lean_inc(v_recordedDeps_3155_);
lean_inc(v_traceState_3154_);
lean_inc(v_auxDeclNGen_3153_);
lean_inc(v_ngen_3152_);
lean_inc(v_nextMacroScope_3151_);
lean_inc(v_env_3150_);
lean_dec(v___x_3149_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3175_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3162_ = lean_box(0);
v___x_3163_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3142_);
v___x_3164_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3164_, 0, v_declName_3142_);
lean_ctor_set(v___x_3164_, 1, v_levelParams_3141_);
lean_ctor_set(v___x_3164_, 2, v_type_3143_);
lean_ctor_set(v___x_3164_, 3, v_value_3144_);
lean_ctor_set(v___x_3164_, 4, v_recArgPos_3136_);
lean_ctor_set(v___x_3164_, 5, v_declNames_3135_);
lean_ctor_set(v___x_3164_, 6, v_fixedParamPerms_3137_);
v___x_3165_ = 0;
v___x_3166_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3163_, v_env_3150_, v_declName_3142_, v___x_3164_, v___x_3165_);
v___x_3167_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 5, v___x_3167_);
lean_ctor_set(v___x_3160_, 0, v___x_3166_);
v___x_3169_ = v___x_3160_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3166_);
lean_ctor_set(v_reuseFailAlloc_3174_, 1, v_nextMacroScope_3151_);
lean_ctor_set(v_reuseFailAlloc_3174_, 2, v_ngen_3152_);
lean_ctor_set(v_reuseFailAlloc_3174_, 3, v_auxDeclNGen_3153_);
lean_ctor_set(v_reuseFailAlloc_3174_, 4, v_traceState_3154_);
lean_ctor_set(v_reuseFailAlloc_3174_, 5, v___x_3167_);
lean_ctor_set(v_reuseFailAlloc_3174_, 6, v_recordedDeps_3155_);
lean_ctor_set(v_reuseFailAlloc_3174_, 7, v_messages_3156_);
lean_ctor_set(v_reuseFailAlloc_3174_, 8, v_infoState_3157_);
lean_ctor_set(v_reuseFailAlloc_3174_, 9, v_snapshotTasks_3158_);
v___x_3169_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
lean_object* v___x_3170_; lean_object* v___x_3172_; 
v___x_3170_ = lean_st_ref_put(v_a_3139_, v___x_3169_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3162_);
v___x_3172_ = v___x_3147_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3162_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
else
{
lean_dec_ref(v_value_3144_);
lean_dec_ref(v_type_3143_);
lean_dec(v_declName_3142_);
lean_dec(v_levelParams_3141_);
lean_dec_ref(v_fixedParamPerms_3137_);
lean_dec(v_recArgPos_3136_);
lean_dec_ref(v_declNames_3135_);
return v___x_3145_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Structural_registerEqnsInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_preDef_3134_ = stack[0].m_obj;
lean_object* v_declNames_3135_ = stack[1].m_obj;
lean_object* v_recArgPos_3136_ = stack[2].m_obj;
lean_object* v_fixedParamPerms_3137_ = stack[3].m_obj;
lean_object* v_a_3138_ = stack[4].m_obj;
lean_object* v_a_3139_ = stack[5].m_obj;
lean_object* v_res_3179_;
v_res_3179_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3134_, v_declNames_3135_, v_recArgPos_3136_, v_fixedParamPerms_3137_, v_a_3138_, v_a_3139_);
stack->m_obj
 = v_res_3179_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3180_, lean_object* v_declNames_3181_, lean_object* v_recArgPos_3182_, lean_object* v_fixedParamPerms_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3180_, v_declNames_3181_, v_recArgPos_3182_, v_fixedParamPerms_3183_, v_a_3184_, v_a_3185_);
lean_dec(v_a_3185_);
lean_dec_ref(v_a_3184_);
return v_res_3187_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(lean_object* v_e_3188_, lean_object* v_k_3189_, uint8_t v_cleanupAnnotations_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___f_3196_; uint8_t v___x_3197_; uint8_t v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___f_3196_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3196_, 0, v_k_3189_);
v___x_3197_ = 1;
v___x_3198_ = 0;
v___x_3199_ = lean_box(0);
v___x_3200_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3188_, v___x_3197_, v___x_3198_, v___x_3197_, v___x_3198_, v___x_3199_, v___f_3196_, v_cleanupAnnotations_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3200_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
v_a_3209_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3200_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3200_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3188_ = stack[0].m_obj;
lean_object* v_k_3189_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_3190_ = stack[2].m_num;
lean_object* v___y_3191_ = stack[3].m_obj;
lean_object* v___y_3192_ = stack[4].m_obj;
lean_object* v___y_3193_ = stack[5].m_obj;
lean_object* v___y_3194_ = stack[6].m_obj;
lean_object* v_res_3217_;
v_res_3217_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_e_3188_, v_k_3189_, v_cleanupAnnotations_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
stack->m_obj
 = v_res_3217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg___boxed(lean_object* v_e_3218_, lean_object* v_k_3219_, lean_object* v_cleanupAnnotations_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3226_; lean_object* v_res_3227_; 
v_cleanupAnnotations_boxed_3226_ = lean_unbox(v_cleanupAnnotations_3220_);
v_res_3227_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_e_3218_, v_k_3219_, v_cleanupAnnotations_boxed_3226_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
return v_res_3227_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_00_u03b1_3228_, lean_object* v_e_3229_, lean_object* v_k_3230_, uint8_t v_cleanupAnnotations_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_e_3229_, v_k_3230_, v_cleanupAnnotations_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3229_ = stack[1].m_obj;
lean_object* v_k_3230_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_3231_ = stack[3].m_num;
lean_object* v___y_3232_ = stack[4].m_obj;
lean_object* v___y_3233_ = stack[5].m_obj;
lean_object* v___y_3234_ = stack[6].m_obj;
lean_object* v___y_3235_ = stack[7].m_obj;
lean_object* v_res_3238_;
v_res_3238_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_box(0), v_e_3229_, v_k_3230_, v_cleanupAnnotations_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
stack->m_obj
 = v_res_3238_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_00_u03b1_3239_, lean_object* v_e_3240_, lean_object* v_k_3241_, lean_object* v_cleanupAnnotations_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3248_; lean_object* v_res_3249_; 
v_cleanupAnnotations_boxed_3248_ = lean_unbox(v_cleanupAnnotations_3242_);
v_res_3249_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_00_u03b1_3239_, v_e_3240_, v_k_3241_, v_cleanupAnnotations_boxed_3248_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3249_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3250_, uint8_t v_isExporting_3251_, lean_object* v___x_3252_, lean_object* v___y_3253_, lean_object* v___x_3254_, lean_object* v_a_x3f_3255_){
_start:
{
lean_object* v___x_3257_; lean_object* v_env_3258_; lean_object* v_nextMacroScope_3259_; lean_object* v_ngen_3260_; lean_object* v_auxDeclNGen_3261_; lean_object* v_traceState_3262_; lean_object* v_recordedDeps_3263_; lean_object* v_messages_3264_; lean_object* v_infoState_3265_; lean_object* v_snapshotTasks_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3291_; 
v___x_3257_ = lean_st_ref_take(v___y_3250_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
v_nextMacroScope_3259_ = lean_ctor_get(v___x_3257_, 1);
v_ngen_3260_ = lean_ctor_get(v___x_3257_, 2);
v_auxDeclNGen_3261_ = lean_ctor_get(v___x_3257_, 3);
v_traceState_3262_ = lean_ctor_get(v___x_3257_, 4);
v_recordedDeps_3263_ = lean_ctor_get(v___x_3257_, 6);
v_messages_3264_ = lean_ctor_get(v___x_3257_, 7);
v_infoState_3265_ = lean_ctor_get(v___x_3257_, 8);
v_snapshotTasks_3266_ = lean_ctor_get(v___x_3257_, 9);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3291_ == 0)
{
lean_object* v_unused_3292_; 
v_unused_3292_ = lean_ctor_get(v___x_3257_, 5);
lean_dec(v_unused_3292_);
v___x_3268_ = v___x_3257_;
v_isShared_3269_ = v_isSharedCheck_3291_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_snapshotTasks_3266_);
lean_inc(v_infoState_3265_);
lean_inc(v_messages_3264_);
lean_inc(v_recordedDeps_3263_);
lean_inc(v_traceState_3262_);
lean_inc(v_auxDeclNGen_3261_);
lean_inc(v_ngen_3260_);
lean_inc(v_nextMacroScope_3259_);
lean_inc(v_env_3258_);
lean_dec(v___x_3257_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3291_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3270_ = l_Lean_Environment_setExporting(v_env_3258_, v_isExporting_3251_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 5, v___x_3252_);
lean_ctor_set(v___x_3268_, 0, v___x_3270_);
v___x_3272_ = v___x_3268_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v_nextMacroScope_3259_);
lean_ctor_set(v_reuseFailAlloc_3290_, 2, v_ngen_3260_);
lean_ctor_set(v_reuseFailAlloc_3290_, 3, v_auxDeclNGen_3261_);
lean_ctor_set(v_reuseFailAlloc_3290_, 4, v_traceState_3262_);
lean_ctor_set(v_reuseFailAlloc_3290_, 5, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3290_, 6, v_recordedDeps_3263_);
lean_ctor_set(v_reuseFailAlloc_3290_, 7, v_messages_3264_);
lean_ctor_set(v_reuseFailAlloc_3290_, 8, v_infoState_3265_);
lean_ctor_set(v_reuseFailAlloc_3290_, 9, v_snapshotTasks_3266_);
v___x_3272_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_mctx_3275_; lean_object* v_zetaDeltaFVarIds_3276_; lean_object* v_postponed_3277_; lean_object* v_diag_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3288_; 
v___x_3273_ = lean_st_ref_put(v___y_3250_, v___x_3272_);
v___x_3274_ = lean_st_ref_take(v___y_3253_);
v_mctx_3275_ = lean_ctor_get(v___x_3274_, 0);
v_zetaDeltaFVarIds_3276_ = lean_ctor_get(v___x_3274_, 2);
v_postponed_3277_ = lean_ctor_get(v___x_3274_, 3);
v_diag_3278_ = lean_ctor_get(v___x_3274_, 4);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3288_ == 0)
{
lean_object* v_unused_3289_; 
v_unused_3289_ = lean_ctor_get(v___x_3274_, 1);
lean_dec(v_unused_3289_);
v___x_3280_ = v___x_3274_;
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_diag_3278_);
lean_inc(v_postponed_3277_);
lean_inc(v_zetaDeltaFVarIds_3276_);
lean_inc(v_mctx_3275_);
lean_dec(v___x_3274_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3282_ = lean_box(0);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v___x_3254_);
v___x_3284_ = v___x_3280_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_mctx_3275_);
lean_ctor_set(v_reuseFailAlloc_3287_, 1, v___x_3254_);
lean_ctor_set(v_reuseFailAlloc_3287_, 2, v_zetaDeltaFVarIds_3276_);
lean_ctor_set(v_reuseFailAlloc_3287_, 3, v_postponed_3277_);
lean_ctor_set(v_reuseFailAlloc_3287_, 4, v_diag_3278_);
v___x_3284_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3285_ = lean_st_ref_put(v___y_3253_, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3282_);
return v___x_3286_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3250_ = stack[0].m_obj;
uint8_t v_isExporting_3251_ = stack[1].m_num;
lean_object* v___x_3252_ = stack[2].m_obj;
lean_object* v___y_3253_ = stack[3].m_obj;
lean_object* v___x_3254_ = stack[4].m_obj;
lean_object* v_a_x3f_3255_ = stack[5].m_obj;
lean_object* v_res_3293_;
v_res_3293_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3250_, v_isExporting_3251_, v___x_3252_, v___y_3253_, v___x_3254_, v_a_x3f_3255_);
stack->m_obj
 = v_res_3293_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3294_, lean_object* v_isExporting_3295_, lean_object* v___x_3296_, lean_object* v___y_3297_, lean_object* v___x_3298_, lean_object* v_a_x3f_3299_, lean_object* v___y_3300_){
_start:
{
uint8_t v_isExporting_boxed_3301_; lean_object* v_res_3302_; 
v_isExporting_boxed_3301_ = lean_unbox(v_isExporting_3295_);
v_res_3302_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3294_, v_isExporting_boxed_3301_, v___x_3296_, v___y_3297_, v___x_3298_, v_a_x3f_3299_);
lean_dec(v_a_x3f_3299_);
lean_dec(v___y_3297_);
lean_dec(v___y_3294_);
return v_res_3302_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3304_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
lean_ctor_set(v___x_3304_, 2, v___x_3303_);
lean_ctor_set(v___x_3304_, 3, v___x_3303_);
lean_ctor_set(v___x_3304_, 4, v___x_3303_);
lean_ctor_set(v___x_3304_, 5, v___x_3303_);
return v___x_3304_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3305_, uint8_t v_isExporting_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; lean_object* v_env_3313_; lean_object* v___x_3314_; uint8_t v_isModule_3315_; 
v___x_3312_ = lean_st_ref_get(v___y_3310_);
v_env_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_ref(v_env_3313_);
lean_dec(v___x_3312_);
v___x_3314_ = l_Lean_Environment_header(v_env_3313_);
v_isModule_3315_ = lean_ctor_get_uint8(v___x_3314_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3314_);
if (v_isModule_3315_ == 0)
{
lean_object* v___x_3316_; 
lean_dec_ref(v_env_3313_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
v___x_3316_ = lean_apply_5(v_x_3305_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, lean_box(0));
return v___x_3316_;
}
else
{
uint8_t v_isExporting_3317_; 
v_isExporting_3317_ = lean_ctor_get_uint8(v_env_3313_, sizeof(void*)*13);
lean_dec_ref(v_env_3313_);
if (v_isExporting_3306_ == 0)
{
if (v_isExporting_3317_ == 0)
{
lean_object* v___x_3384_; 
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
v___x_3384_ = lean_apply_5(v_x_3305_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, lean_box(0));
return v___x_3384_;
}
else
{
goto v___jp_3318_;
}
}
else
{
if (v_isExporting_3317_ == 0)
{
goto v___jp_3318_;
}
else
{
lean_object* v___x_3385_; 
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
v___x_3385_ = lean_apply_5(v_x_3305_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, lean_box(0));
return v___x_3385_;
}
}
v___jp_3318_:
{
lean_object* v___x_3319_; lean_object* v_env_3320_; lean_object* v_nextMacroScope_3321_; lean_object* v_ngen_3322_; lean_object* v_auxDeclNGen_3323_; lean_object* v_traceState_3324_; lean_object* v_recordedDeps_3325_; lean_object* v_messages_3326_; lean_object* v_infoState_3327_; lean_object* v_snapshotTasks_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3382_; 
v___x_3319_ = lean_st_ref_take(v___y_3310_);
v_env_3320_ = lean_ctor_get(v___x_3319_, 0);
v_nextMacroScope_3321_ = lean_ctor_get(v___x_3319_, 1);
v_ngen_3322_ = lean_ctor_get(v___x_3319_, 2);
v_auxDeclNGen_3323_ = lean_ctor_get(v___x_3319_, 3);
v_traceState_3324_ = lean_ctor_get(v___x_3319_, 4);
v_recordedDeps_3325_ = lean_ctor_get(v___x_3319_, 6);
v_messages_3326_ = lean_ctor_get(v___x_3319_, 7);
v_infoState_3327_ = lean_ctor_get(v___x_3319_, 8);
v_snapshotTasks_3328_ = lean_ctor_get(v___x_3319_, 9);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3382_ == 0)
{
lean_object* v_unused_3383_; 
v_unused_3383_ = lean_ctor_get(v___x_3319_, 5);
lean_dec(v_unused_3383_);
v___x_3330_ = v___x_3319_;
v_isShared_3331_ = v_isSharedCheck_3382_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_snapshotTasks_3328_);
lean_inc(v_infoState_3327_);
lean_inc(v_messages_3326_);
lean_inc(v_recordedDeps_3325_);
lean_inc(v_traceState_3324_);
lean_inc(v_auxDeclNGen_3323_);
lean_inc(v_ngen_3322_);
lean_inc(v_nextMacroScope_3321_);
lean_inc(v_env_3320_);
lean_dec(v___x_3319_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3382_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3332_ = l_Lean_Environment_setExporting(v_env_3320_, v_isExporting_3306_);
v___x_3333_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 5, v___x_3333_);
lean_ctor_set(v___x_3330_, 0, v___x_3332_);
v___x_3335_ = v___x_3330_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3332_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_nextMacroScope_3321_);
lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_ngen_3322_);
lean_ctor_set(v_reuseFailAlloc_3381_, 3, v_auxDeclNGen_3323_);
lean_ctor_set(v_reuseFailAlloc_3381_, 4, v_traceState_3324_);
lean_ctor_set(v_reuseFailAlloc_3381_, 5, v___x_3333_);
lean_ctor_set(v_reuseFailAlloc_3381_, 6, v_recordedDeps_3325_);
lean_ctor_set(v_reuseFailAlloc_3381_, 7, v_messages_3326_);
lean_ctor_set(v_reuseFailAlloc_3381_, 8, v_infoState_3327_);
lean_ctor_set(v_reuseFailAlloc_3381_, 9, v_snapshotTasks_3328_);
v___x_3335_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_mctx_3338_; lean_object* v_zetaDeltaFVarIds_3339_; lean_object* v_postponed_3340_; lean_object* v_diag_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3379_; 
v___x_3336_ = lean_st_ref_put(v___y_3310_, v___x_3335_);
v___x_3337_ = lean_st_ref_take(v___y_3308_);
v_mctx_3338_ = lean_ctor_get(v___x_3337_, 0);
v_zetaDeltaFVarIds_3339_ = lean_ctor_get(v___x_3337_, 2);
v_postponed_3340_ = lean_ctor_get(v___x_3337_, 3);
v_diag_3341_ = lean_ctor_get(v___x_3337_, 4);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; 
v_unused_3380_ = lean_ctor_get(v___x_3337_, 1);
lean_dec(v_unused_3380_);
v___x_3343_ = v___x_3337_;
v_isShared_3344_ = v_isSharedCheck_3379_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_diag_3341_);
lean_inc(v_postponed_3340_);
lean_inc(v_zetaDeltaFVarIds_3339_);
lean_inc(v_mctx_3338_);
lean_dec(v___x_3337_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3379_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3345_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3344_ == 0)
{
lean_ctor_set(v___x_3343_, 1, v___x_3345_);
v___x_3347_ = v___x_3343_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_mctx_3338_);
lean_ctor_set(v_reuseFailAlloc_3378_, 1, v___x_3345_);
lean_ctor_set(v_reuseFailAlloc_3378_, 2, v_zetaDeltaFVarIds_3339_);
lean_ctor_set(v_reuseFailAlloc_3378_, 3, v_postponed_3340_);
lean_ctor_set(v_reuseFailAlloc_3378_, 4, v_diag_3341_);
v___x_3347_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v_r_3349_; 
v___x_3348_ = lean_st_ref_put(v___y_3308_, v___x_3347_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v___y_3308_);
lean_inc_ref(v___y_3307_);
v_r_3349_ = lean_apply_5(v_x_3305_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_, lean_box(0));
if (lean_obj_tag(v_r_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3366_; 
v_a_3350_ = lean_ctor_get(v_r_3349_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_r_3349_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3352_ = v_r_3349_;
v_isShared_3353_ = v_isSharedCheck_3366_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v_r_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3366_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
lean_inc(v_a_3350_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set_tag(v___x_3352_, 1);
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
v___x_3356_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3310_, v_isExporting_3317_, v___x_3333_, v___y_3308_, v___x_3345_, v___x_3355_);
lean_dec_ref(v___x_3355_);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3363_ == 0)
{
lean_object* v_unused_3364_; 
v_unused_3364_ = lean_ctor_get(v___x_3356_, 0);
lean_dec(v_unused_3364_);
v___x_3358_ = v___x_3356_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_dec(v___x_3356_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v_a_3350_);
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3350_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
v_a_3367_ = lean_ctor_get(v_r_3349_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v_r_3349_, 1);
v___x_3368_ = lean_box(0);
v___x_3369_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3310_, v_isExporting_3317_, v___x_3333_, v___y_3308_, v___x_3345_, v___x_3368_);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3376_ == 0)
{
lean_object* v_unused_3377_; 
v_unused_3377_ = lean_ctor_get(v___x_3369_, 0);
lean_dec(v_unused_3377_);
v___x_3371_ = v___x_3369_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3369_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set_tag(v___x_3371_, 1);
lean_ctor_set(v___x_3371_, 0, v_a_3367_);
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3367_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3305_ = stack[0].m_obj;
uint8_t v_isExporting_3306_ = stack[1].m_num;
lean_object* v___y_3307_ = stack[2].m_obj;
lean_object* v___y_3308_ = stack[3].m_obj;
lean_object* v___y_3309_ = stack[4].m_obj;
lean_object* v___y_3310_ = stack[5].m_obj;
lean_object* v_res_3386_;
v_res_3386_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3305_, v_isExporting_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
stack->m_obj
 = v_res_3386_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3387_, lean_object* v_isExporting_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
uint8_t v_isExporting_boxed_3394_; lean_object* v_res_3395_; 
v_isExporting_boxed_3394_ = lean_unbox(v_isExporting_3388_);
v_res_3395_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3387_, v_isExporting_boxed_3394_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_);
lean_dec(v___y_3392_);
lean_dec_ref(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
return v_res_3395_;
}
}
lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3396_, uint8_t v_when_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
if (v_when_3397_ == 0)
{
lean_object* v___x_3403_; 
lean_inc(v___y_3401_);
lean_inc_ref(v___y_3400_);
lean_inc(v___y_3399_);
lean_inc_ref(v___y_3398_);
v___x_3403_ = lean_apply_5(v_x_3396_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, lean_box(0));
return v___x_3403_;
}
else
{
uint8_t v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = 0;
v___x_3405_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3396_, v___x_3404_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v___x_3405_;
}
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3396_ = stack[0].m_obj;
uint8_t v_when_3397_ = stack[1].m_num;
lean_object* v___y_3398_ = stack[2].m_obj;
lean_object* v___y_3399_ = stack[3].m_obj;
lean_object* v___y_3400_ = stack[4].m_obj;
lean_object* v___y_3401_ = stack[5].m_obj;
lean_object* v_res_3406_;
v_res_3406_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3396_, v_when_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
stack->m_obj
 = v_res_3406_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3407_, lean_object* v_when_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v_when_boxed_3414_; lean_object* v_res_3415_; 
v_when_boxed_3414_ = lean_unbox(v_when_3408_);
v_res_3415_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3407_, v_when_boxed_3414_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3416_, lean_object* v_a_3417_){
_start:
{
if (lean_obj_tag(v_a_3416_) == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = l_List_reverse___redArg(v_a_3417_);
return v___x_3418_;
}
else
{
lean_object* v_head_3419_; lean_object* v_tail_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3429_; 
v_head_3419_ = lean_ctor_get(v_a_3416_, 0);
v_tail_3420_ = lean_ctor_get(v_a_3416_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_a_3416_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3422_ = v_a_3416_;
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_tail_3420_);
lean_inc(v_head_3419_);
lean_dec(v_a_3416_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3429_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3424_; lean_object* v___x_3426_; 
v___x_3424_ = l_Lean_mkLevelParam(v_head_3419_);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 1, v_a_3417_);
lean_ctor_set(v___x_3422_, 0, v___x_3424_);
v___x_3426_ = v___x_3422_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3424_);
lean_ctor_set(v_reuseFailAlloc_3428_, 1, v_a_3417_);
v___x_3426_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
v_a_3416_ = v_tail_3420_;
v_a_3417_ = v___x_3426_;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3430_, lean_object* v_declName_3431_, lean_object* v_name_3432_, lean_object* v_xs_3433_, lean_object* v_body_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; lean_object* v_us_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3440_ = lean_box(0);
lean_inc(v_levelParams_3430_);
v_us_3441_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3430_, v___x_3440_);
lean_inc(v_declName_3431_);
v___x_3442_ = l_Lean_mkConst(v_declName_3431_, v_us_3441_);
v___x_3443_ = l_Lean_mkAppN(v___x_3442_, v_xs_3433_);
v___x_3444_ = l_Lean_Meta_mkEq(v___x_3443_, v_body_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; uint8_t v___x_3447_; lean_object* v___x_3448_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc_n(v_a_3445_, 2);
lean_dec_ref_known(v___x_3444_, 1);
v___x_3446_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3446_, 0, v_declName_3431_);
lean_closure_set(v___x_3446_, 1, v_a_3445_);
v___x_3447_ = 1;
v___x_3448_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3446_, v___x_3447_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3448_) == 0)
{
lean_object* v_a_3449_; uint8_t v___x_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; 
v_a_3449_ = lean_ctor_get(v___x_3448_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v___x_3448_, 1);
v___x_3450_ = 0;
v___x_3451_ = 1;
v___x_3452_ = l_Lean_Meta_mkForallFVars(v_xs_3433_, v_a_3445_, v___x_3450_, v___x_3447_, v___x_3447_, v___x_3451_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = l_Lean_Meta_letToHave(v_a_3453_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = l_Lean_Meta_mkLambdaFVars(v_xs_3433_, v_a_3449_, v___x_3450_, v___x_3447_, v___x_3450_, v___x_3447_, v___x_3451_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
lean_inc_n(v_name_3432_, 2);
v___x_3458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3458_, 0, v_name_3432_);
lean_ctor_set(v___x_3458_, 1, v_levelParams_3430_);
lean_ctor_set(v___x_3458_, 2, v_a_3455_);
v___x_3459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3459_, 0, v_name_3432_);
lean_ctor_set(v___x_3459_, 1, v___x_3440_);
v___x_3460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v_a_3457_);
lean_ctor_set(v___x_3460_, 2, v___x_3459_);
v___x_3461_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
v___x_3462_ = l_Lean_addDecl(v___x_3461_, v___x_3450_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; 
lean_dec_ref_known(v___x_3462_, 1);
v___x_3463_ = l_Lean_inferDefEqAttr(v_name_3432_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
return v___x_3463_;
}
else
{
lean_dec(v_name_3432_);
return v___x_3462_;
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v_a_3455_);
lean_dec(v_name_3432_);
lean_dec(v_levelParams_3430_);
v_a_3464_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3456_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3456_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_dec(v_a_3449_);
lean_dec(v_name_3432_);
lean_dec(v_levelParams_3430_);
v_a_3472_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3454_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3454_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_a_3449_);
lean_dec(v_name_3432_);
lean_dec(v_levelParams_3430_);
v_a_3480_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3452_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3452_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v_a_3445_);
lean_dec(v_name_3432_);
lean_dec(v_levelParams_3430_);
v_a_3488_ = lean_ctor_get(v___x_3448_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3448_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3448_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec(v_name_3432_);
lean_dec(v_declName_3431_);
lean_dec(v_levelParams_3430_);
v_a_3496_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3444_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3444_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_levelParams_3430_ = stack[0].m_obj;
lean_object* v_declName_3431_ = stack[1].m_obj;
lean_object* v_name_3432_ = stack[2].m_obj;
lean_object* v_xs_3433_ = stack[3].m_obj;
lean_object* v_body_3434_ = stack[4].m_obj;
lean_object* v___y_3435_ = stack[5].m_obj;
lean_object* v___y_3436_ = stack[6].m_obj;
lean_object* v___y_3437_ = stack[7].m_obj;
lean_object* v___y_3438_ = stack[8].m_obj;
lean_object* v_res_3504_;
v_res_3504_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3430_, v_declName_3431_, v_name_3432_, v_xs_3433_, v_body_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
stack->m_obj
 = v_res_3504_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3505_, lean_object* v_declName_3506_, lean_object* v_name_3507_, lean_object* v_xs_3508_, lean_object* v_body_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3505_, v_declName_3506_, v_name_3507_, v_xs_3508_, v_body_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v_xs_3508_);
return v_res_3515_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(lean_object* v_o_3516_, lean_object* v_k_3517_, uint8_t v_v_3518_){
_start:
{
lean_object* v_map_3519_; uint8_t v_hasTrace_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3534_; 
v_map_3519_ = lean_ctor_get(v_o_3516_, 0);
v_hasTrace_3520_ = lean_ctor_get_uint8(v_o_3516_, sizeof(void*)*1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_o_3516_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3522_ = v_o_3516_;
v_isShared_3523_ = v_isSharedCheck_3534_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_map_3519_);
lean_dec(v_o_3516_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3534_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3524_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3524_, 0, v_v_3518_);
lean_inc(v_k_3517_);
v___x_3525_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3517_, v___x_3524_, v_map_3519_);
if (v_hasTrace_3520_ == 0)
{
lean_object* v___x_3526_; uint8_t v___x_3527_; lean_object* v___x_3529_; 
v___x_3526_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3527_ = l_Lean_Name_isPrefixOf(v___x_3526_, v_k_3517_);
lean_dec(v_k_3517_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3525_);
v___x_3529_ = v___x_3522_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3525_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_ctor_set_uint8(v___x_3529_, sizeof(void*)*1, v___x_3527_);
return v___x_3529_;
}
}
else
{
lean_object* v___x_3532_; 
lean_dec(v_k_3517_);
if (v_isShared_3523_ == 0)
{
lean_ctor_set(v___x_3522_, 0, v___x_3525_);
v___x_3532_ = v___x_3522_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3525_);
lean_ctor_set_uint8(v_reuseFailAlloc_3533_, sizeof(void*)*1, v_hasTrace_3520_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_3516_ = stack[0].m_obj;
lean_object* v_k_3517_ = stack[1].m_obj;
uint8_t v_v_3518_ = stack[2].m_num;
lean_object* v_res_3535_;
v_res_3535_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(v_o_3516_, v_k_3517_, v_v_3518_);
stack->m_obj
 = v_res_3535_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4___boxed(lean_object* v_o_3536_, lean_object* v_k_3537_, lean_object* v_v_3538_){
_start:
{
uint8_t v_v_boxed_3539_; lean_object* v_res_3540_; 
v_v_boxed_3539_ = lean_unbox(v_v_3538_);
v_res_3540_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(v_o_3536_, v_k_3537_, v_v_boxed_3539_);
return v_res_3540_;
}
}
lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_3541_, lean_object* v_opt_3542_, uint8_t v_val_3543_){
_start:
{
lean_object* v_name_3544_; lean_object* v___x_3545_; 
v_name_3544_ = lean_ctor_get(v_opt_3542_, 0);
lean_inc(v_name_3544_);
lean_dec_ref(v_opt_3542_);
v___x_3545_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(v_opts_3541_, v_name_3544_, v_val_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_3541_ = stack[0].m_obj;
lean_object* v_opt_3542_ = stack[1].m_obj;
uint8_t v_val_3543_ = stack[2].m_num;
lean_object* v_res_3546_;
v_res_3546_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_opts_3541_, v_opt_3542_, v_val_3543_);
stack->m_obj
 = v_res_3546_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_3547_, lean_object* v_opt_3548_, lean_object* v_val_3549_){
_start:
{
uint8_t v_val_boxed_3550_; lean_object* v_res_3551_; 
v_val_boxed_3550_ = lean_unbox(v_val_3549_);
v_res_3551_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_opts_3547_, v_opt_3548_, v_val_boxed_3550_);
return v_res_3551_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3552_, lean_object* v_info_3553_, lean_object* v_name_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_){
_start:
{
lean_object* v_toCold_3560_; lean_object* v_levelParams_3561_; lean_object* v_value_3562_; lean_object* v_currRecDepth_3563_; lean_object* v_ref_3564_; uint8_t v_suppressElabErrors_3565_; uint8_t v_isRecordingDeps_3566_; lean_object* v_fileName_3567_; lean_object* v_fileMap_3568_; lean_object* v_options_3569_; lean_object* v_currNamespace_3570_; lean_object* v_openDecls_3571_; lean_object* v_initHeartbeats_3572_; lean_object* v_maxHeartbeats_3573_; lean_object* v_quotContext_3574_; lean_object* v_currMacroScope_3575_; lean_object* v_cancelTk_x3f_3576_; lean_object* v_inheritedTraceOptions_3577_; lean_object* v___f_3578_; uint8_t v___x_3579_; uint16_t v___y_3581_; lean_object* v___y_3582_; lean_object* v_fileName_3583_; lean_object* v_fileMap_3584_; lean_object* v_currNamespace_3585_; lean_object* v_openDecls_3586_; lean_object* v_initHeartbeats_3587_; lean_object* v_maxHeartbeats_3588_; lean_object* v_quotContext_3589_; lean_object* v_currMacroScope_3590_; lean_object* v_cancelTk_x3f_3591_; lean_object* v_inheritedTraceOptions_3592_; lean_object* v_currRecDepth_3593_; lean_object* v_ref_3594_; uint8_t v_suppressElabErrors_3595_; uint8_t v_isRecordingDeps_3596_; lean_object* v___y_3597_; uint8_t v___y_3604_; uint16_t v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3629_; 
v_toCold_3560_ = lean_ctor_get(v_a_3557_, 0);
v_levelParams_3561_ = lean_ctor_get(v_info_3553_, 1);
lean_inc(v_levelParams_3561_);
v_value_3562_ = lean_ctor_get(v_info_3553_, 3);
lean_inc_ref(v_value_3562_);
lean_dec_ref(v_info_3553_);
v_currRecDepth_3563_ = lean_ctor_get(v_a_3557_, 1);
v_ref_3564_ = lean_ctor_get(v_a_3557_, 2);
v_suppressElabErrors_3565_ = lean_ctor_get_uint8(v_a_3557_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3566_ = lean_ctor_get_uint8(v_a_3557_, sizeof(void*)*3 + 3);
v_fileName_3567_ = lean_ctor_get(v_toCold_3560_, 0);
v_fileMap_3568_ = lean_ctor_get(v_toCold_3560_, 1);
v_options_3569_ = lean_ctor_get(v_toCold_3560_, 2);
v_currNamespace_3570_ = lean_ctor_get(v_toCold_3560_, 4);
v_openDecls_3571_ = lean_ctor_get(v_toCold_3560_, 5);
v_initHeartbeats_3572_ = lean_ctor_get(v_toCold_3560_, 6);
v_maxHeartbeats_3573_ = lean_ctor_get(v_toCold_3560_, 7);
v_quotContext_3574_ = lean_ctor_get(v_toCold_3560_, 8);
v_currMacroScope_3575_ = lean_ctor_get(v_toCold_3560_, 9);
v_cancelTk_x3f_3576_ = lean_ctor_get(v_toCold_3560_, 10);
v_inheritedTraceOptions_3577_ = lean_ctor_get(v_toCold_3560_, 11);
v___f_3578_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3578_, 0, v_levelParams_3561_);
lean_closure_set(v___f_3578_, 1, v_declName_3552_);
lean_closure_set(v___f_3578_, 2, v_name_3554_);
v___x_3579_ = 0;
if (v_isRecordingDeps_3566_ == 0)
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3569_);
v___x_3640_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_options_3569_, v___x_3639_, v_isRecordingDeps_3566_);
v___y_3629_ = v___x_3640_;
goto v___jp_3628_;
}
else
{
lean_object* v___x_3641_; 
lean_inc_ref(v_options_3569_);
v___x_3641_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_3569_);
v___y_3629_ = v___x_3641_;
goto v___jp_3628_;
}
v___jp_3580_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3598_ = l_Lean_maxRecDepth;
v___x_3599_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___y_3582_, v___x_3598_);
v___x_3600_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3600_, 0, v_fileName_3583_);
lean_ctor_set(v___x_3600_, 1, v_fileMap_3584_);
lean_ctor_set(v___x_3600_, 2, v___y_3582_);
lean_ctor_set(v___x_3600_, 3, v___x_3599_);
lean_ctor_set(v___x_3600_, 4, v_currNamespace_3585_);
lean_ctor_set(v___x_3600_, 5, v_openDecls_3586_);
lean_ctor_set(v___x_3600_, 6, v_initHeartbeats_3587_);
lean_ctor_set(v___x_3600_, 7, v_maxHeartbeats_3588_);
lean_ctor_set(v___x_3600_, 8, v_quotContext_3589_);
lean_ctor_set(v___x_3600_, 9, v_currMacroScope_3590_);
lean_ctor_set(v___x_3600_, 10, v_cancelTk_x3f_3591_);
lean_ctor_set(v___x_3600_, 11, v_inheritedTraceOptions_3592_);
lean_inc(v_ref_3594_);
lean_inc(v_currRecDepth_3593_);
v___x_3601_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
lean_ctor_set(v___x_3601_, 1, v_currRecDepth_3593_);
lean_ctor_set(v___x_3601_, 2, v_ref_3594_);
lean_ctor_set_uint16(v___x_3601_, sizeof(void*)*3, v___y_3581_);
lean_ctor_set_uint8(v___x_3601_, sizeof(void*)*3 + 2, v_suppressElabErrors_3595_);
lean_ctor_set_uint8(v___x_3601_, sizeof(void*)*3 + 3, v_isRecordingDeps_3596_);
v___x_3602_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_value_3562_, v___f_3578_, v___x_3579_, v_a_3555_, v_a_3556_, v___x_3601_, v___y_3597_);
lean_dec_ref_known(v___x_3601_, 3);
return v___x_3602_;
}
v___jp_3603_:
{
lean_object* v___x_3607_; lean_object* v_env_3608_; lean_object* v_nextMacroScope_3609_; lean_object* v_ngen_3610_; lean_object* v_auxDeclNGen_3611_; lean_object* v_traceState_3612_; lean_object* v_recordedDeps_3613_; lean_object* v_messages_3614_; lean_object* v_infoState_3615_; lean_object* v_snapshotTasks_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3626_; 
v___x_3607_ = lean_st_ref_take(v_a_3558_);
v_env_3608_ = lean_ctor_get(v___x_3607_, 0);
v_nextMacroScope_3609_ = lean_ctor_get(v___x_3607_, 1);
v_ngen_3610_ = lean_ctor_get(v___x_3607_, 2);
v_auxDeclNGen_3611_ = lean_ctor_get(v___x_3607_, 3);
v_traceState_3612_ = lean_ctor_get(v___x_3607_, 4);
v_recordedDeps_3613_ = lean_ctor_get(v___x_3607_, 6);
v_messages_3614_ = lean_ctor_get(v___x_3607_, 7);
v_infoState_3615_ = lean_ctor_get(v___x_3607_, 8);
v_snapshotTasks_3616_ = lean_ctor_get(v___x_3607_, 9);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v___x_3607_, 5);
lean_dec(v_unused_3627_);
v___x_3618_ = v___x_3607_;
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_snapshotTasks_3616_);
lean_inc(v_infoState_3615_);
lean_inc(v_messages_3614_);
lean_inc(v_recordedDeps_3613_);
lean_inc(v_traceState_3612_);
lean_inc(v_auxDeclNGen_3611_);
lean_inc(v_ngen_3610_);
lean_inc(v_nextMacroScope_3609_);
lean_inc(v_env_3608_);
lean_dec(v___x_3607_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3626_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3623_; 
v___x_3620_ = l_Lean_Kernel_enableDiag(v_env_3608_, v___y_3604_);
v___x_3621_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3619_ == 0)
{
lean_ctor_set(v___x_3618_, 5, v___x_3621_);
lean_ctor_set(v___x_3618_, 0, v___x_3620_);
v___x_3623_ = v___x_3618_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_nextMacroScope_3609_);
lean_ctor_set(v_reuseFailAlloc_3625_, 2, v_ngen_3610_);
lean_ctor_set(v_reuseFailAlloc_3625_, 3, v_auxDeclNGen_3611_);
lean_ctor_set(v_reuseFailAlloc_3625_, 4, v_traceState_3612_);
lean_ctor_set(v_reuseFailAlloc_3625_, 5, v___x_3621_);
lean_ctor_set(v_reuseFailAlloc_3625_, 6, v_recordedDeps_3613_);
lean_ctor_set(v_reuseFailAlloc_3625_, 7, v_messages_3614_);
lean_ctor_set(v_reuseFailAlloc_3625_, 8, v_infoState_3615_);
lean_ctor_set(v_reuseFailAlloc_3625_, 9, v_snapshotTasks_3616_);
v___x_3623_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_st_ref_put(v_a_3558_, v___x_3623_);
lean_inc_ref(v_inheritedTraceOptions_3577_);
lean_inc(v_cancelTk_x3f_3576_);
lean_inc(v_currMacroScope_3575_);
lean_inc(v_quotContext_3574_);
lean_inc(v_maxHeartbeats_3573_);
lean_inc(v_initHeartbeats_3572_);
lean_inc(v_openDecls_3571_);
lean_inc(v_currNamespace_3570_);
lean_inc_ref(v_fileMap_3568_);
lean_inc_ref(v_fileName_3567_);
v___y_3581_ = v___y_3605_;
v___y_3582_ = v___y_3606_;
v_fileName_3583_ = v_fileName_3567_;
v_fileMap_3584_ = v_fileMap_3568_;
v_currNamespace_3585_ = v_currNamespace_3570_;
v_openDecls_3586_ = v_openDecls_3571_;
v_initHeartbeats_3587_ = v_initHeartbeats_3572_;
v_maxHeartbeats_3588_ = v_maxHeartbeats_3573_;
v_quotContext_3589_ = v_quotContext_3574_;
v_currMacroScope_3590_ = v_currMacroScope_3575_;
v_cancelTk_x3f_3591_ = v_cancelTk_x3f_3576_;
v_inheritedTraceOptions_3592_ = v_inheritedTraceOptions_3577_;
v_currRecDepth_3593_ = v_currRecDepth_3563_;
v_ref_3594_ = v_ref_3564_;
v_suppressElabErrors_3595_ = v_suppressElabErrors_3565_;
v_isRecordingDeps_3596_ = v_isRecordingDeps_3566_;
v___y_3597_ = v_a_3558_;
goto v___jp_3580_;
}
}
}
v___jp_3628_:
{
uint16_t v___x_3630_; lean_object* v___x_3631_; lean_object* v_env_3632_; uint8_t v___x_3633_; uint16_t v___x_3634_; uint16_t v___x_3635_; uint16_t v___x_3636_; uint8_t v___x_3637_; 
v___x_3630_ = l_Lean_OptionFlags_ofOptions(v___y_3629_);
v___x_3631_ = lean_st_ref_get(v_a_3558_);
v_env_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc_ref(v_env_3632_);
lean_dec(v___x_3631_);
v___x_3633_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3632_);
lean_dec_ref(v_env_3632_);
v___x_3634_ = 512;
v___x_3635_ = lean_uint16_land(v___x_3630_, v___x_3634_);
v___x_3636_ = 0;
v___x_3637_ = lean_uint16_dec_eq(v___x_3635_, v___x_3636_);
if (v___x_3637_ == 0)
{
if (v___x_3633_ == 0)
{
uint8_t v___x_3638_; 
v___x_3638_ = 1;
v___y_3604_ = v___x_3638_;
v___y_3605_ = v___x_3630_;
v___y_3606_ = v___y_3629_;
goto v___jp_3603_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3577_);
lean_inc(v_cancelTk_x3f_3576_);
lean_inc(v_currMacroScope_3575_);
lean_inc(v_quotContext_3574_);
lean_inc(v_maxHeartbeats_3573_);
lean_inc(v_initHeartbeats_3572_);
lean_inc(v_openDecls_3571_);
lean_inc(v_currNamespace_3570_);
lean_inc_ref(v_fileMap_3568_);
lean_inc_ref(v_fileName_3567_);
v___y_3581_ = v___x_3630_;
v___y_3582_ = v___y_3629_;
v_fileName_3583_ = v_fileName_3567_;
v_fileMap_3584_ = v_fileMap_3568_;
v_currNamespace_3585_ = v_currNamespace_3570_;
v_openDecls_3586_ = v_openDecls_3571_;
v_initHeartbeats_3587_ = v_initHeartbeats_3572_;
v_maxHeartbeats_3588_ = v_maxHeartbeats_3573_;
v_quotContext_3589_ = v_quotContext_3574_;
v_currMacroScope_3590_ = v_currMacroScope_3575_;
v_cancelTk_x3f_3591_ = v_cancelTk_x3f_3576_;
v_inheritedTraceOptions_3592_ = v_inheritedTraceOptions_3577_;
v_currRecDepth_3593_ = v_currRecDepth_3563_;
v_ref_3594_ = v_ref_3564_;
v_suppressElabErrors_3595_ = v_suppressElabErrors_3565_;
v_isRecordingDeps_3596_ = v_isRecordingDeps_3566_;
v___y_3597_ = v_a_3558_;
goto v___jp_3580_;
}
}
else
{
if (v___x_3633_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3577_);
lean_inc(v_cancelTk_x3f_3576_);
lean_inc(v_currMacroScope_3575_);
lean_inc(v_quotContext_3574_);
lean_inc(v_maxHeartbeats_3573_);
lean_inc(v_initHeartbeats_3572_);
lean_inc(v_openDecls_3571_);
lean_inc(v_currNamespace_3570_);
lean_inc_ref(v_fileMap_3568_);
lean_inc_ref(v_fileName_3567_);
v___y_3581_ = v___x_3630_;
v___y_3582_ = v___y_3629_;
v_fileName_3583_ = v_fileName_3567_;
v_fileMap_3584_ = v_fileMap_3568_;
v_currNamespace_3585_ = v_currNamespace_3570_;
v_openDecls_3586_ = v_openDecls_3571_;
v_initHeartbeats_3587_ = v_initHeartbeats_3572_;
v_maxHeartbeats_3588_ = v_maxHeartbeats_3573_;
v_quotContext_3589_ = v_quotContext_3574_;
v_currMacroScope_3590_ = v_currMacroScope_3575_;
v_cancelTk_x3f_3591_ = v_cancelTk_x3f_3576_;
v_inheritedTraceOptions_3592_ = v_inheritedTraceOptions_3577_;
v_currRecDepth_3593_ = v_currRecDepth_3563_;
v_ref_3594_ = v_ref_3564_;
v_suppressElabErrors_3595_ = v_suppressElabErrors_3565_;
v_isRecordingDeps_3596_ = v_isRecordingDeps_3566_;
v___y_3597_ = v_a_3558_;
goto v___jp_3580_;
}
else
{
v___y_3604_ = v___x_3579_;
v___y_3605_ = v___x_3630_;
v___y_3606_ = v___y_3629_;
goto v___jp_3603_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3552_ = stack[0].m_obj;
lean_object* v_info_3553_ = stack[1].m_obj;
lean_object* v_name_3554_ = stack[2].m_obj;
lean_object* v_a_3555_ = stack[3].m_obj;
lean_object* v_a_3556_ = stack[4].m_obj;
lean_object* v_a_3557_ = stack[5].m_obj;
lean_object* v_a_3558_ = stack[6].m_obj;
lean_object* v_res_3642_;
v_res_3642_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3552_, v_info_3553_, v_name_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
stack->m_obj
 = v_res_3642_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3643_, lean_object* v_info_3644_, lean_object* v_name_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3643_, v_info_3644_, v_name_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3651_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3652_, lean_object* v_x_3653_, uint8_t v_isExporting_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
lean_object* v___x_3660_; 
v___x_3660_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3653_, v_isExporting_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3653_ = stack[1].m_obj;
uint8_t v_isExporting_3654_ = stack[2].m_num;
lean_object* v___y_3655_ = stack[3].m_obj;
lean_object* v___y_3656_ = stack[4].m_obj;
lean_object* v___y_3657_ = stack[5].m_obj;
lean_object* v___y_3658_ = stack[6].m_obj;
lean_object* v_res_3661_;
v_res_3661_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_box(0), v_x_3653_, v_isExporting_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
stack->m_obj
 = v_res_3661_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3662_, lean_object* v_x_3663_, lean_object* v_isExporting_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_isExporting_boxed_3670_; lean_object* v_res_3671_; 
v_isExporting_boxed_3670_ = lean_unbox(v_isExporting_3664_);
v_res_3671_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3662_, v_x_3663_, v_isExporting_boxed_3670_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3671_;
}
}
lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3672_, lean_object* v_x_3673_, uint8_t v_when_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3673_, v_when_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3680_;
}
}
LEAN_EXPORT void l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3673_ = stack[1].m_obj;
uint8_t v_when_3674_ = stack[2].m_num;
lean_object* v___y_3675_ = stack[3].m_obj;
lean_object* v___y_3676_ = stack[4].m_obj;
lean_object* v___y_3677_ = stack[5].m_obj;
lean_object* v___y_3678_ = stack[6].m_obj;
lean_object* v_res_3681_;
v_res_3681_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_box(0), v_x_3673_, v_when_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
stack->m_obj
 = v_res_3681_;
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_x_3683_, lean_object* v_when_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
uint8_t v_when_boxed_3690_; lean_object* v_res_3691_; 
v_when_boxed_3690_ = lean_unbox(v_when_3684_);
v_res_3691_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3682_, v_x_3683_, v_when_boxed_3690_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
return v_res_3691_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3692_, lean_object* v_info_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_env_3701_; lean_object* v_declName_3702_; lean_object* v_declNames_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3699_ = lean_box(0);
v___x_3700_ = lean_st_ref_get(v_a_3697_);
v_env_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc_ref(v_env_3701_);
lean_dec(v___x_3700_);
v_declName_3702_ = lean_ctor_get(v_info_3693_, 0);
v_declNames_3703_ = lean_ctor_get(v_info_3693_, 5);
v___x_3704_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3702_);
v___x_3705_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3701_, v_declName_3702_, v___x_3704_);
v___x_3706_ = lean_unsigned_to_nat(0u);
v___x_3707_ = lean_array_get(v___x_3699_, v_declNames_3703_, v___x_3706_);
lean_inc_n(v___x_3705_, 2);
lean_inc(v_declName_3692_);
v___x_3708_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3708_, 0, v_declName_3692_);
lean_closure_set(v___x_3708_, 1, v_info_3693_);
lean_closure_set(v___x_3708_, 2, v___x_3705_);
v___x_3709_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3709_, 0, lean_box(0));
lean_closure_set(v___x_3709_, 1, v_declName_3692_);
lean_closure_set(v___x_3709_, 2, v___x_3708_);
v___x_3710_ = l_Lean_Meta_realizeConst(v___x_3707_, v___x_3705_, v___x_3709_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3717_ == 0)
{
lean_object* v_unused_3718_; 
v_unused_3718_ = lean_ctor_get(v___x_3710_, 0);
lean_dec(v_unused_3718_);
v___x_3712_ = v___x_3710_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_dec(v___x_3710_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3705_);
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3705_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v___x_3705_);
v_a_3719_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3710_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3710_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3692_ = stack[0].m_obj;
lean_object* v_info_3693_ = stack[1].m_obj;
lean_object* v_a_3694_ = stack[2].m_obj;
lean_object* v_a_3695_ = stack[3].m_obj;
lean_object* v_a_3696_ = stack[4].m_obj;
lean_object* v_a_3697_ = stack[5].m_obj;
lean_object* v_res_3727_;
v_res_3727_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3692_, v_info_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_);
stack->m_obj
 = v_res_3727_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3728_, lean_object* v_info_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_){
_start:
{
lean_object* v_res_3735_; 
v_res_3735_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3728_, v_info_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
return v_res_3735_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v_env_3744_; lean_object* v___x_3745_; lean_object* v_toEnvExtension_3746_; lean_object* v_asyncMode_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; 
v___x_3742_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3743_ = lean_st_ref_get(v_a_3740_);
v_env_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc_ref(v_env_3744_);
lean_dec(v___x_3743_);
v___x_3745_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3746_ = lean_ctor_get(v___x_3745_, 0);
v_asyncMode_3747_ = lean_ctor_get(v_toEnvExtension_3746_, 2);
v___x_3748_ = 0;
lean_inc(v_declName_3736_);
v___x_3749_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3742_, v___x_3745_, v_env_3744_, v_declName_3736_, v_asyncMode_3747_, v___x_3748_);
if (lean_obj_tag(v___x_3749_) == 1)
{
lean_object* v_val_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3774_; 
v_val_3750_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3752_ = v___x_3749_;
v_isShared_3753_ = v_isSharedCheck_3774_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_val_3750_);
lean_dec(v___x_3749_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3774_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3754_; 
v___x_3754_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3736_, v_val_3750_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3765_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3757_ = v___x_3754_;
v_isShared_3758_ = v_isSharedCheck_3765_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3754_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3765_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3753_ == 0)
{
lean_ctor_set(v___x_3752_, 0, v_a_3755_);
v___x_3760_ = v___x_3752_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3762_; 
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 0, v___x_3760_);
v___x_3762_ = v___x_3757_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3752_);
v_a_3766_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3754_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3754_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_dec(v___x_3749_);
lean_dec(v_declName_3736_);
v___x_3775_ = lean_box(0);
v___x_3776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
return v___x_3776_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3736_ = stack[0].m_obj;
lean_object* v_a_3737_ = stack[1].m_obj;
lean_object* v_a_3738_ = stack[2].m_obj;
lean_object* v_a_3739_ = stack[3].m_obj;
lean_object* v_a_3740_ = stack[4].m_obj;
lean_object* v_res_3777_;
v_res_3777_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_);
stack->m_obj
 = v_res_3777_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_);
lean_dec(v_a_3782_);
lean_dec_ref(v_a_3781_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
return v_res_3784_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3785_, lean_object* v_a_3786_){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v_env_3790_; lean_object* v___x_3791_; lean_object* v_toEnvExtension_3792_; lean_object* v_asyncMode_3793_; uint8_t v___x_3794_; lean_object* v___x_3795_; 
v___x_3788_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3789_ = lean_st_ref_get(v_a_3786_);
v_env_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc_ref(v_env_3790_);
lean_dec(v___x_3789_);
v___x_3791_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3792_ = lean_ctor_get(v___x_3791_, 0);
v_asyncMode_3793_ = lean_ctor_get(v_toEnvExtension_3792_, 2);
v___x_3794_ = 0;
v___x_3795_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3788_, v___x_3791_, v_env_3790_, v_declName_3785_, v_asyncMode_3793_, v___x_3794_);
if (lean_obj_tag(v___x_3795_) == 1)
{
lean_object* v_val_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3805_; 
v_val_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3805_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_val_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3805_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v_recArgPos_3800_; lean_object* v___x_3802_; 
v_recArgPos_3800_ = lean_ctor_get(v_val_3796_, 4);
lean_inc(v_recArgPos_3800_);
lean_dec(v_val_3796_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v_recArgPos_3800_);
v___x_3802_ = v___x_3798_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_recArgPos_3800_);
v___x_3802_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
lean_object* v___x_3803_; 
v___x_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
lean_dec(v___x_3795_);
v___x_3806_ = lean_box(0);
v___x_3807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
return v___x_3807_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3785_ = stack[0].m_obj;
lean_object* v_a_3786_ = stack[1].m_obj;
lean_object* v_res_3808_;
v_res_3808_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3785_, v_a_3786_);
stack->m_obj
 = v_res_3808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3809_, v_a_3810_);
lean_dec(v_a_3810_);
return v_res_3812_;
}
}
lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_){
_start:
{
lean_object* v___x_3817_; 
lean_dec_ref(v_a_3814_);
v___x_3817_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3813_, v_a_3815_);
lean_dec(v_a_3815_);
return v___x_3817_;
}
}
LEAN_EXPORT void lean_get_structural_rec_arg_pos_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_3813_ = stack[0].m_obj;
lean_object* v_a_3814_ = stack[1].m_obj;
lean_object* v_a_3815_ = stack[2].m_obj;
lean_object* v_res_3818_;
v_res_3818_ = lean_get_structural_rec_arg_pos(v_declName_3813_, v_a_3814_, v_a_3815_);
stack->m_obj
 = v_res_3818_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v_res_3823_; 
v_res_3823_ = lean_get_structural_rec_arg_pos(v_declName_3819_, v_a_3820_, v_a_3821_);
return v_res_3823_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3881_ = lean_unsigned_to_nat(2295916746u);
v___x_3882_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3883_ = l_Lean_Name_num___override(v___x_3882_, v___x_3881_);
return v___x_3883_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3886_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3887_ = l_Lean_Name_str___override(v___x_3886_, v___x_3885_);
return v___x_3887_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3889_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3890_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3891_ = l_Lean_Name_str___override(v___x_3890_, v___x_3889_);
return v___x_3891_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3892_ = lean_unsigned_to_nat(2u);
v___x_3893_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3894_ = l_Lean_Name_num___override(v___x_3893_, v___x_3892_);
return v___x_3894_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3897_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3896_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v___x_3898_; uint8_t v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_dec_ref_known(v___x_3897_, 1);
v___x_3898_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_3899_ = 0;
v___x_3900_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3901_ = l_Lean_registerTraceClass(v___x_3898_, v___x_3899_, v___x_3900_);
return v___x_3901_;
}
else
{
return v___x_3897_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3902_;
v_res_3902_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
stack->m_obj
 = v_res_3902_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_3904_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_instInhabitedEqnInfo_default = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo_default();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo_default);
l_Lean_Elab_Structural_instInhabitedEqnInfo = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo);
res = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Structural_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Structural_eqnInfoExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_CasesOnStuckLHS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_CasesOnStuckLHS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin);
}
#ifdef __cplusplus
}
#endif
