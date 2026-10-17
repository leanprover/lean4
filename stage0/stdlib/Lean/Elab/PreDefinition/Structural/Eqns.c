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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(lean_object* v_k_18_, lean_object* v_b_19_, lean_object* v_c_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_27_, lean_object* v_b_28_, lean_object* v_c_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0(v_k_27_, v_b_28_, v_c_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(lean_object* v_type_36_, lean_object* v_k_37_, uint8_t v_cleanupAnnotations_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___f_44_; uint8_t v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_44_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_44_, 0, v_k_37_);
v___x_45_ = 0;
v___x_46_ = lean_box(0);
v___x_47_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_45_, v___x_46_, v_type_36_, v___f_44_, v_cleanupAnnotations_38_, v___x_45_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_56_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_47_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_47_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___boxed(lean_object* v_type_64_, lean_object* v_k_65_, lean_object* v_cleanupAnnotations_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_72_; lean_object* v_res_73_; 
v_cleanupAnnotations_boxed_72_ = lean_unbox(v_cleanupAnnotations_66_);
v_res_73_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_type_64_, v_k_65_, v_cleanupAnnotations_boxed_72_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(lean_object* v_00_u03b1_74_, lean_object* v_type_75_, lean_object* v_k_76_, uint8_t v_cleanupAnnotations_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_type_75_, v_k_76_, v_cleanupAnnotations_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___boxed(lean_object* v_00_u03b1_84_, lean_object* v_type_85_, lean_object* v_k_86_, lean_object* v_cleanupAnnotations_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_93_; lean_object* v_res_94_; 
v_cleanupAnnotations_boxed_93_ = lean_unbox(v_cleanupAnnotations_87_);
v_res_94_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1(v_00_u03b1_84_, v_type_85_, v_k_86_, v_cleanupAnnotations_boxed_93_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(lean_object* v___x_95_, lean_object* v_k_96_, lean_object* v___x_97_, lean_object* v_x_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = l_Subarray_copy___redArg(v___x_95_);
lean_inc_ref(v_x_98_);
v___x_105_ = l_Lean_mkAppN(v_x_98_, v___x_104_);
lean_dec_ref(v___x_104_);
lean_inc(v___y_102_);
lean_inc_ref(v___y_101_);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
v___x_106_ = lean_apply_8(v_k_96_, v___x_97_, v_x_98_, v___x_105_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, lean_box(0));
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed(lean_object* v___x_107_, lean_object* v_k_108_, lean_object* v___x_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2(v___x_107_, v_k_108_, v___x_109_, v_x_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(lean_object* v_typeName_117_, lean_object* v_idx_118_, lean_object* v_x_119_, lean_object* v_k_120_, lean_object* v_brecOnApp_121_, lean_object* v_x_122_, lean_object* v_c_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = l_Lean_mkProj(v_typeName_117_, v_idx_118_, v_c_123_);
v___x_130_ = l_Lean_mkAppN(v___x_129_, v_x_119_);
lean_inc(v___y_127_);
lean_inc_ref(v___y_126_);
lean_inc(v___y_125_);
lean_inc_ref(v___y_124_);
v___x_131_ = lean_apply_8(v_k_120_, v_brecOnApp_121_, v_x_122_, v___x_130_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, lean_box(0));
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed(lean_object* v_typeName_132_, lean_object* v_idx_133_, lean_object* v_x_134_, lean_object* v_k_135_, lean_object* v_brecOnApp_136_, lean_object* v_x_137_, lean_object* v_c_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0(v_typeName_132_, v_idx_133_, v_x_134_, v_k_135_, v_brecOnApp_136_, v_x_137_, v_c_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec_ref(v_x_134_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(lean_object* v_k_145_, lean_object* v_b_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v___x_152_; 
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
v___x_152_ = lean_apply_6(v_k_145_, v_b_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, lean_box(0));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_153_, lean_object* v_b_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0(v_k_153_, v_b_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(lean_object* v_name_161_, uint8_t v_bi_162_, lean_object* v_type_163_, lean_object* v_k_164_, uint8_t v_kind_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___f_171_; lean_object* v___x_172_; 
v___f_171_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_171_, 0, v_k_164_);
v___x_172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_161_, v_bi_162_, v_type_163_, v___f_171_, v_kind_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_172_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_172_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg___boxed(lean_object* v_name_189_, lean_object* v_bi_190_, lean_object* v_type_191_, lean_object* v_k_192_, lean_object* v_kind_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_bi_boxed_199_; uint8_t v_kind_boxed_200_; lean_object* v_res_201_; 
v_bi_boxed_199_ = lean_unbox(v_bi_190_);
v_kind_boxed_200_ = lean_unbox(v_kind_193_);
v_res_201_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_189_, v_bi_boxed_199_, v_type_191_, v_k_192_, v_kind_boxed_200_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(lean_object* v_name_202_, lean_object* v_type_203_, lean_object* v_k_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
uint8_t v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; 
v___x_210_ = 0;
v___x_211_ = 0;
v___x_212_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_202_, v___x_210_, v_type_203_, v_k_204_, v___x_211_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg___boxed(lean_object* v_name_213_, lean_object* v_type_214_, lean_object* v_k_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v_name_213_, v_type_214_, v_k_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(lean_object* v_msgData_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; lean_object* v_env_229_; uint8_t v___x_230_; lean_object* v_env_231_; lean_object* v___x_232_; lean_object* v_toCold_233_; lean_object* v_mctx_234_; lean_object* v_lctx_235_; lean_object* v_options_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = 0;
v_env_231_ = l_Lean_Environment_setRecordingDeps(v_env_229_, v___x_230_);
v___x_232_ = lean_st_ref_get(v___y_224_);
v_toCold_233_ = lean_ctor_get(v___y_225_, 0);
v_mctx_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref(v_mctx_234_);
lean_dec(v___x_232_);
v_lctx_235_ = lean_ctor_get(v___y_223_, 2);
v_options_236_ = lean_ctor_get(v_toCold_233_, 2);
lean_inc_ref(v_options_236_);
lean_inc_ref(v_lctx_235_);
v___x_237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_237_, 0, v_env_231_);
lean_ctor_set(v___x_237_, 1, v_mctx_234_);
lean_ctor_set(v___x_237_, 2, v_lctx_235_);
lean_ctor_set(v___x_237_, 3, v_options_236_);
v___x_238_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_msgData_222_);
v___x_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0___boxed(lean_object* v_msgData_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msgData_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_263_; 
v_ref_253_ = lean_ctor_get(v___y_250_, 2);
v___x_254_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_263_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_263_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_261_; 
lean_inc(v_ref_253_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v_ref_253_);
lean_ctor_set(v___x_259_, 1, v_a_255_);
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
lean_ctor_set(v___x_257_, 0, v___x_259_);
v___x_261_ = v___x_257_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg___boxed(lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(lean_object* v_xs_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_array_get_size(v_xs_271_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed(lean_object* v_xs_280_, lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(v_xs_280_, v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec_ref(v_x_281_);
lean_dec_ref(v_xs_280_);
return v_res_287_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_288_; lean_object* v_dummy_289_; 
v___x_288_ = lean_box(0);
v_dummy_289_ = l_Lean_Expr_sort___override(v___x_288_);
return v_dummy_289_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__0));
v___x_292_ = l_Lean_stringToMessageData(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(lean_object* v_e_297_, lean_object* v_k_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___y_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; 
if (lean_obj_tag(v_x_299_) == 5)
{
lean_object* v_fn_316_; lean_object* v_arg_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_fn_316_ = lean_ctor_get(v_x_299_, 0);
lean_inc_ref(v_fn_316_);
v_arg_317_ = lean_ctor_get(v_x_299_, 1);
lean_inc_ref(v_arg_317_);
lean_dec_ref_known(v_x_299_, 2);
v___x_318_ = lean_array_set(v_x_300_, v_x_301_, v_arg_317_);
v___x_319_ = lean_unsigned_to_nat(1u);
v___x_320_ = lean_nat_sub(v_x_301_, v___x_319_);
lean_dec(v_x_301_);
v_x_299_ = v_fn_316_;
v_x_300_ = v___x_318_;
v_x_301_ = v___x_320_;
goto _start;
}
else
{
lean_dec(v_x_301_);
if (lean_obj_tag(v_x_299_) == 11)
{
lean_object* v_typeName_322_; lean_object* v_idx_323_; lean_object* v_struct_324_; lean_object* v___f_325_; lean_object* v___x_326_; 
lean_dec_ref(v_e_297_);
v_typeName_322_ = lean_ctor_get(v_x_299_, 0);
lean_inc(v_typeName_322_);
v_idx_323_ = lean_ctor_get(v_x_299_, 1);
lean_inc(v_idx_323_);
v_struct_324_ = lean_ctor_get(v_x_299_, 2);
lean_inc_ref(v_struct_324_);
lean_dec_ref_known(v_x_299_, 3);
v___f_325_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_325_, 0, v_typeName_322_);
lean_closure_set(v___f_325_, 1, v_idx_323_);
lean_closure_set(v___f_325_, 2, v_x_300_);
lean_closure_set(v___f_325_, 3, v_k_298_);
v___x_326_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_struct_324_, v___f_325_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_326_;
}
else
{
if (lean_obj_tag(v_x_299_) == 4)
{
lean_object* v_declName_327_; lean_object* v___f_328_; lean_object* v___x_329_; lean_object* v_env_330_; uint8_t v___x_331_; 
v_declName_327_ = lean_ctor_get(v_x_299_, 0);
v___f_328_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2));
v___x_329_ = lean_st_ref_get(v___y_305_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
lean_inc(v_declName_327_);
v___x_331_ = l_Lean_isBRecOnRecursor(v_env_330_, v_declName_327_);
if (v___x_331_ == 0)
{
lean_dec_ref_known(v_x_299_, 2);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_k_298_);
v___y_308_ = v___y_302_;
v___y_309_ = v___y_303_;
v___y_310_ = v___y_304_;
v___y_311_ = v___y_305_;
goto v___jp_307_;
}
else
{
lean_object* v___x_332_; 
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc_ref(v_x_299_);
v___x_332_ = lean_infer_type(v_x_299_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; uint8_t v___x_334_; lean_object* v___x_335_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_332_, 1);
v___x_334_ = 0;
v___x_335_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_a_333_, v___f_328_, v___x_334_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = lean_array_get_size(v_x_300_);
v___x_338_ = lean_nat_dec_le(v_a_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v_a_336_);
lean_dec_ref_known(v_x_299_, 2);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_k_298_);
v___y_308_ = v___y_302_;
v___y_309_ = v___y_303_;
v___y_310_ = v___y_304_;
v___y_311_ = v___y_305_;
goto v___jp_307_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___f_344_; lean_object* v___x_345_; 
lean_dec_ref(v_e_297_);
v___x_339_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_336_);
lean_inc_ref(v_x_300_);
v___x_340_ = l_Array_toSubarray___redArg(v_x_300_, v___x_339_, v_a_336_);
v___x_341_ = l_Subarray_copy___redArg(v___x_340_);
v___x_342_ = l_Lean_mkAppN(v_x_299_, v___x_341_);
lean_dec_ref(v___x_341_);
v___x_343_ = l_Array_toSubarray___redArg(v_x_300_, v_a_336_, v___x_337_);
lean_inc_ref(v___x_342_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_344_, 0, v___x_343_);
lean_closure_set(v___f_344_, 1, v_k_298_);
lean_closure_set(v___f_344_, 2, v___x_342_);
lean_inc(v___y_305_);
lean_inc_ref(v___y_304_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
v___x_345_ = lean_infer_type(v___x_342_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4));
v___x_348_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v___x_347_, v_a_346_, v___f_344_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_348_;
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec_ref(v___f_344_);
v_a_349_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_345_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_345_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref_known(v_x_299_, 2);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_k_298_);
lean_dec_ref(v_e_297_);
v_a_357_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_335_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_335_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref_known(v_x_299_, 2);
lean_dec_ref(v_x_300_);
lean_dec_ref(v_k_298_);
lean_dec_ref(v_e_297_);
v_a_365_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_332_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_332_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_300_);
lean_dec_ref(v_x_299_);
lean_dec_ref(v_k_298_);
v___y_308_ = v___y_302_;
v___y_309_ = v___y_303_;
v___y_310_ = v___y_304_;
v___y_311_ = v___y_305_;
goto v___jp_307_;
}
}
}
v___jp_307_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_312_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1);
v___x_313_ = l_Lean_indentExpr(v_e_297_);
v___x_314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_314_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(lean_object* v_e_373_, lean_object* v_k_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_dummy_380_; lean_object* v_nargs_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_dummy_380_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_381_ = l_Lean_Expr_getAppNumArgs(v_e_373_);
lean_inc(v_nargs_381_);
v___x_382_ = lean_mk_array(v_nargs_381_, v_dummy_380_);
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_sub(v_nargs_381_, v___x_383_);
lean_dec(v_nargs_381_);
lean_inc_ref(v_e_373_);
v___x_385_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_373_, v_k_374_, v_e_373_, v___x_382_, v___x_384_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___boxed(lean_object* v_e_386_, lean_object* v_k_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_386_, v_k_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object* v_e_394_, lean_object* v_k_395_, lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_394_, v_k_395_, v_x_396_, v_x_397_, v_x_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_object* v_00_u03b1_405_, lean_object* v_e_406_, lean_object* v_k_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_406_, v_k_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___boxed(lean_object* v_00_u03b1_414_, lean_object* v_e_415_, lean_object* v_k_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(v_00_u03b1_414_, v_e_415_, v_k_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_object* v_00_u03b1_423_, lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___boxed(lean_object* v_00_u03b1_431_, lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(v_00_u03b1_431_, v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_object* v_00_u03b1_439_, lean_object* v_name_440_, uint8_t v_bi_441_, lean_object* v_type_442_, lean_object* v_k_443_, uint8_t v_kind_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_440_, v_bi_441_, v_type_442_, v_k_443_, v_kind_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_451_, lean_object* v_name_452_, lean_object* v_bi_453_, lean_object* v_type_454_, lean_object* v_k_455_, lean_object* v_kind_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v_bi_boxed_462_; uint8_t v_kind_boxed_463_; lean_object* v_res_464_; 
v_bi_boxed_462_ = lean_unbox(v_bi_453_);
v_kind_boxed_463_ = lean_unbox(v_kind_456_);
v_res_464_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(v_00_u03b1_451_, v_name_452_, v_bi_boxed_462_, v_type_454_, v_k_455_, v_kind_boxed_463_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_object* v_00_u03b1_465_, lean_object* v_name_466_, lean_object* v_type_467_, lean_object* v_k_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v_name_466_, v_type_467_, v_k_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___boxed(lean_object* v_00_u03b1_475_, lean_object* v_name_476_, lean_object* v_type_477_, lean_object* v_k_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(v_00_u03b1_475_, v_name_476_, v_type_477_, v_k_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_object* v_00_u03b1_485_, lean_object* v_e_486_, lean_object* v_k_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_486_, v_k_487_, v_x_488_, v_x_489_, v_x_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___boxed(lean_object* v_00_u03b1_497_, lean_object* v_e_498_, lean_object* v_k_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(v_00_u03b1_497_, v_e_498_, v_k_499_, v_x_500_, v_x_501_, v_x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object* v___x_509_, uint8_t v___x_510_, lean_object* v_brecOnApp_511_, lean_object* v_x_512_, lean_object* v_c_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_mkEq(v_c_513_, v___x_509_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_mk_empty_array_with_capacity(v___x_521_);
v___x_523_ = lean_array_push(v___x_522_, v_x_512_);
v___x_524_ = 0;
v___x_525_ = 1;
v___x_526_ = l_Lean_Meta_mkLambdaFVars(v___x_523_, v_a_520_, v___x_524_, v___x_510_, v___x_524_, v___x_510_, v___x_525_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec_ref(v___x_523_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_535_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_535_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_535_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_brecOnApp_511_);
lean_ctor_set(v___x_531_, 1, v_a_527_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_531_);
v___x_533_ = v___x_529_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v_brecOnApp_511_);
v_a_536_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_526_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_526_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_x_512_);
lean_dec_ref(v_brecOnApp_511_);
v_a_544_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_519_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_519_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed(lean_object* v___x_552_, lean_object* v___x_553_, lean_object* v_brecOnApp_554_, lean_object* v_x_555_, lean_object* v_c_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
uint8_t v___x_553__boxed_562_; lean_object* v_res_563_; 
v___x_553__boxed_562_ = lean_unbox(v___x_553_);
v_res_563_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(v___x_552_, v___x_553__boxed_562_, v_brecOnApp_554_, v_x_555_, v_c_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_563_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(lean_object* v_goal_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_577_ = lean_unsigned_to_nat(3u);
v___x_578_ = l_Lean_Expr_isAppOfArity(v_goal_570_, v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3);
v___x_580_ = l_Lean_indentExpr(v_goal_570_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_581_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___f_587_; lean_object* v___x_588_; 
v___x_583_ = l_Lean_Expr_appFn_x21(v_goal_570_);
v___x_584_ = l_Lean_Expr_appArg_x21(v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = l_Lean_Expr_appArg_x21(v_goal_570_);
lean_dec_ref(v_goal_570_);
v___x_586_ = lean_box(v___x_578_);
v___f_587_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed), 10, 2);
lean_closure_set(v___f_587_, 0, v___x_585_);
lean_closure_set(v___f_587_, 1, v___x_586_);
v___x_588_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v___x_584_, v___f_587_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___boxed(lean_object* v_goal_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_goal_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(lean_object* v_mvarId_596_, lean_object* v_x_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_596_, v_x_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_603_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_603_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_620_, lean_object* v_x_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_620_, v_x_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_object* v_00_u03b1_628_, lean_object* v_mvarId_629_, lean_object* v_x_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_629_, v_x_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___boxed(lean_object* v_00_u03b1_637_, lean_object* v_mvarId_638_, lean_object* v_x_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(v_00_u03b1_637_, v_mvarId_638_, v_x_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_645_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(lean_object* v_declName_646_, lean_object* v_x_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = lean_name_eq(v_x_647_, v_declName_646_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed(lean_object* v_declName_649_, lean_object* v_x_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(v_declName_649_, v_x_650_);
lean_dec(v_x_650_);
lean_dec(v_declName_649_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(lean_object* v_mvarId_653_, lean_object* v___f_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
lean_inc(v_mvarId_653_);
v___x_660_ = l_Lean_MVarId_getType_x27(v_mvarId_653_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_730_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_730_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_730_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_730_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_666_ = lean_unsigned_to_nat(3u);
v___x_667_ = l_Lean_Expr_isAppOfArity(v_a_661_, v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec(v_a_661_);
lean_dec_ref(v___f_654_);
lean_dec(v_mvarId_653_);
v___x_668_ = lean_box(0);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_668_);
v___x_670_ = v___x_663_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; 
lean_del_object(v___x_663_);
v___x_672_ = l_Lean_Expr_appFn_x21(v_a_661_);
v___x_673_ = l_Lean_Expr_appArg_x21(v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = l_Lean_Expr_appArg_x21(v_a_661_);
lean_dec(v_a_661_);
v___x_675_ = l_Lean_Expr_consumeMData(v___x_674_);
lean_dec_ref(v___x_674_);
v___x_676_ = 0;
v___x_677_ = l_Lean_Meta_delta_x3f(v___x_675_, v___f_654_, v___x_676_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_721_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_721_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_721_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_721_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
if (lean_obj_tag(v_a_678_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_716_; 
lean_del_object(v___x_680_);
v_val_682_ = lean_ctor_get(v_a_678_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_716_ == 0)
{
v___x_684_ = v_a_678_;
v_isShared_685_ = v_isSharedCheck_716_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v_a_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_716_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_mkEq(v___x_673_, v_val_682_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_653_, v_a_687_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_699_ == 0)
{
v___x_691_ = v___x_688_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_688_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v_a_689_);
v___x_694_ = v___x_684_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 0, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
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
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_684_);
v_a_700_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_688_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_688_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_del_object(v___x_684_);
lean_dec(v_mvarId_653_);
v_a_708_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_686_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_686_);
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
else
{
lean_object* v___x_717_; lean_object* v___x_719_; 
lean_dec(v_a_678_);
lean_dec_ref(v___x_673_);
lean_dec(v_mvarId_653_);
v___x_717_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_717_);
v___x_719_ = v___x_680_;
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
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec_ref(v___x_673_);
lean_dec(v_mvarId_653_);
v_a_722_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_677_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_677_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_727_; 
if (v_isShared_725_ == 0)
{
v___x_727_ = v___x_724_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_722_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
}
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v___f_654_);
lean_dec(v_mvarId_653_);
v_a_731_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_660_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_660_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object* v_mvarId_739_, lean_object* v___f_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(v_mvarId_739_, v___f_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object* v_mvarId_747_, lean_object* v_declName_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___f_754_; lean_object* v___f_755_; lean_object* v___x_756_; 
v___f_754_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_754_, 0, v_declName_748_);
lean_inc(v_mvarId_747_);
v___f_755_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_755_, 0, v_mvarId_747_);
lean_closure_set(v___f_755_, 1, v___f_754_);
v___x_756_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_747_, v___f_755_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object* v_mvarId_757_, lean_object* v_declName_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_757_, v_declName_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
return v_res_764_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(32u);
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_768_ = ((size_t)5ULL);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_unsigned_to_nat(32u);
v___x_771_ = lean_mk_empty_array_with_capacity(v___x_770_);
v___x_772_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0);
v___x_773_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
lean_ctor_set(v___x_773_, 2, v___x_769_);
lean_ctor_set(v___x_773_, 3, v___x_769_);
lean_ctor_set_usize(v___x_773_, 4, v___x_768_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(lean_object* v___y_774_){
_start:
{
lean_object* v___x_776_; lean_object* v_traceState_777_; lean_object* v_traces_778_; lean_object* v___x_779_; lean_object* v_traceState_780_; lean_object* v_env_781_; lean_object* v_nextMacroScope_782_; lean_object* v_ngen_783_; lean_object* v_auxDeclNGen_784_; lean_object* v_cache_785_; lean_object* v_recordedDeps_786_; lean_object* v_messages_787_; lean_object* v_infoState_788_; lean_object* v_snapshotTasks_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_808_; 
v___x_776_ = lean_st_ref_get(v___y_774_);
v_traceState_777_ = lean_ctor_get(v___x_776_, 4);
lean_inc_ref(v_traceState_777_);
lean_dec(v___x_776_);
v_traces_778_ = lean_ctor_get(v_traceState_777_, 0);
lean_inc_ref(v_traces_778_);
lean_dec_ref(v_traceState_777_);
v___x_779_ = lean_st_ref_take(v___y_774_);
v_traceState_780_ = lean_ctor_get(v___x_779_, 4);
v_env_781_ = lean_ctor_get(v___x_779_, 0);
v_nextMacroScope_782_ = lean_ctor_get(v___x_779_, 1);
v_ngen_783_ = lean_ctor_get(v___x_779_, 2);
v_auxDeclNGen_784_ = lean_ctor_get(v___x_779_, 3);
v_cache_785_ = lean_ctor_get(v___x_779_, 5);
v_recordedDeps_786_ = lean_ctor_get(v___x_779_, 6);
v_messages_787_ = lean_ctor_get(v___x_779_, 7);
v_infoState_788_ = lean_ctor_get(v___x_779_, 8);
v_snapshotTasks_789_ = lean_ctor_get(v___x_779_, 9);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_808_ == 0)
{
v___x_791_ = v___x_779_;
v_isShared_792_ = v_isSharedCheck_808_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snapshotTasks_789_);
lean_inc(v_infoState_788_);
lean_inc(v_messages_787_);
lean_inc(v_recordedDeps_786_);
lean_inc(v_cache_785_);
lean_inc(v_traceState_780_);
lean_inc(v_auxDeclNGen_784_);
lean_inc(v_ngen_783_);
lean_inc(v_nextMacroScope_782_);
lean_inc(v_env_781_);
lean_dec(v___x_779_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_808_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
uint64_t v_tid_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_806_; 
v_tid_793_ = lean_ctor_get_uint64(v_traceState_780_, sizeof(void*)*1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_traceState_780_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v_traceState_780_, 0);
lean_dec(v_unused_807_);
v___x_795_ = v_traceState_780_;
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_traceState_780_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set_uint64(v_reuseFailAlloc_805_, sizeof(void*)*1, v_tid_793_);
v___x_799_ = v_reuseFailAlloc_805_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v___x_799_);
v___x_801_ = v___x_791_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_env_781_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_nextMacroScope_782_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_ngen_783_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_auxDeclNGen_784_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_804_, 5, v_cache_785_);
lean_ctor_set(v_reuseFailAlloc_804_, 6, v_recordedDeps_786_);
lean_ctor_set(v_reuseFailAlloc_804_, 7, v_messages_787_);
lean_ctor_set(v_reuseFailAlloc_804_, 8, v_infoState_788_);
lean_ctor_set(v_reuseFailAlloc_804_, 9, v_snapshotTasks_789_);
v___x_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_st_ref_put(v___y_774_, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_traces_778_);
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___boxed(lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_809_);
lean_dec(v___y_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_823_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v_opts_824_, lean_object* v_opt_825_){
_start:
{
lean_object* v_name_826_; lean_object* v_defValue_827_; lean_object* v_map_828_; lean_object* v___x_829_; 
v_name_826_ = lean_ctor_get(v_opt_825_, 0);
v_defValue_827_ = lean_ctor_get(v_opt_825_, 1);
v_map_828_ = lean_ctor_get(v_opts_824_, 0);
v___x_829_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_828_, v_name_826_);
if (lean_obj_tag(v___x_829_) == 0)
{
uint8_t v___x_830_; 
v___x_830_ = lean_unbox(v_defValue_827_);
return v___x_830_;
}
else
{
lean_object* v_val_831_; 
v_val_831_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v___x_829_, 1);
if (lean_obj_tag(v_val_831_) == 1)
{
uint8_t v_v_832_; 
v_v_832_ = lean_ctor_get_uint8(v_val_831_, 0);
lean_dec_ref_known(v_val_831_, 0);
return v_v_832_;
}
else
{
uint8_t v___x_833_; 
lean_dec(v_val_831_);
v___x_833_ = lean_unbox(v_defValue_827_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v_opts_834_, lean_object* v_opt_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_834_, v_opt_835_);
lean_dec_ref(v_opt_835_);
lean_dec_ref(v_opts_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* v_mvarId_841_, lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_848_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_mvarId_841_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_848_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object* v_mvarId_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(v_mvarId_852_, v_x_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec_ref(v_x_853_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* v_____r_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object* v_____r_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_____r_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_875_; double v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_float_of_nat(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v_cls_880_, lean_object* v_msg_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
lean_object* v_ref_887_; lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_934_; 
v_ref_887_ = lean_ctor_get(v___y_884_, 2);
v___x_888_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_934_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_934_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_934_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v_traceState_894_; lean_object* v_env_895_; lean_object* v_nextMacroScope_896_; lean_object* v_ngen_897_; lean_object* v_auxDeclNGen_898_; lean_object* v_cache_899_; lean_object* v_recordedDeps_900_; lean_object* v_messages_901_; lean_object* v_infoState_902_; lean_object* v_snapshotTasks_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_933_; 
v___x_893_ = lean_st_ref_take(v___y_885_);
v_traceState_894_ = lean_ctor_get(v___x_893_, 4);
v_env_895_ = lean_ctor_get(v___x_893_, 0);
v_nextMacroScope_896_ = lean_ctor_get(v___x_893_, 1);
v_ngen_897_ = lean_ctor_get(v___x_893_, 2);
v_auxDeclNGen_898_ = lean_ctor_get(v___x_893_, 3);
v_cache_899_ = lean_ctor_get(v___x_893_, 5);
v_recordedDeps_900_ = lean_ctor_get(v___x_893_, 6);
v_messages_901_ = lean_ctor_get(v___x_893_, 7);
v_infoState_902_ = lean_ctor_get(v___x_893_, 8);
v_snapshotTasks_903_ = lean_ctor_get(v___x_893_, 9);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_933_ == 0)
{
v___x_905_ = v___x_893_;
v_isShared_906_ = v_isSharedCheck_933_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_snapshotTasks_903_);
lean_inc(v_infoState_902_);
lean_inc(v_messages_901_);
lean_inc(v_recordedDeps_900_);
lean_inc(v_cache_899_);
lean_inc(v_traceState_894_);
lean_inc(v_auxDeclNGen_898_);
lean_inc(v_ngen_897_);
lean_inc(v_nextMacroScope_896_);
lean_inc(v_env_895_);
lean_dec(v___x_893_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_933_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
uint64_t v_tid_907_; lean_object* v_traces_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_932_; 
v_tid_907_ = lean_ctor_get_uint64(v_traceState_894_, sizeof(void*)*1);
v_traces_908_ = lean_ctor_get(v_traceState_894_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_traceState_894_);
if (v_isSharedCheck_932_ == 0)
{
v___x_910_ = v_traceState_894_;
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_traces_908_);
lean_dec(v_traceState_894_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_932_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_913_; double v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_912_ = lean_box(0);
v___x_913_ = lean_box(0);
v___x_914_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
v___x_915_ = 0;
v___x_916_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_917_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_917_, 0, v_cls_880_);
lean_ctor_set(v___x_917_, 1, v___x_913_);
lean_ctor_set(v___x_917_, 2, v___x_916_);
lean_ctor_set_float(v___x_917_, sizeof(void*)*3, v___x_914_);
lean_ctor_set_float(v___x_917_, sizeof(void*)*3 + 8, v___x_914_);
lean_ctor_set_uint8(v___x_917_, sizeof(void*)*3 + 16, v___x_915_);
v___x_918_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2));
v___x_919_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v_a_889_);
lean_ctor_set(v___x_919_, 2, v___x_918_);
lean_inc(v_ref_887_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_ref_887_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_PersistentArray_push___redArg(v_traces_908_, v___x_920_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_921_);
v___x_923_ = v___x_910_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_921_);
lean_ctor_set_uint64(v_reuseFailAlloc_931_, sizeof(void*)*1, v_tid_907_);
v___x_923_ = v_reuseFailAlloc_931_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_925_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 4, v___x_923_);
v___x_925_ = v___x_905_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_env_895_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_nextMacroScope_896_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_ngen_897_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_auxDeclNGen_898_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_930_, 5, v_cache_899_);
lean_ctor_set(v_reuseFailAlloc_930_, 6, v_recordedDeps_900_);
lean_ctor_set(v_reuseFailAlloc_930_, 7, v_messages_901_);
lean_ctor_set(v_reuseFailAlloc_930_, 8, v_infoState_902_);
lean_ctor_set(v_reuseFailAlloc_930_, 9, v_snapshotTasks_903_);
v___x_925_ = v_reuseFailAlloc_930_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_st_ref_put(v___y_885_, v___x_925_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_912_);
v___x_928_ = v___x_891_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_912_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_935_, lean_object* v_msg_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_935_, v_msg_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(lean_object* v_opts_943_, lean_object* v_opt_944_){
_start:
{
lean_object* v_name_945_; lean_object* v_defValue_946_; lean_object* v_map_947_; lean_object* v___x_948_; 
v_name_945_ = lean_ctor_get(v_opt_944_, 0);
v_defValue_946_ = lean_ctor_get(v_opt_944_, 1);
v_map_947_ = lean_ctor_get(v_opts_943_, 0);
v___x_948_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_947_, v_name_945_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_inc(v_defValue_946_);
return v_defValue_946_;
}
else
{
lean_object* v_val_949_; 
v_val_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_val_949_);
lean_dec_ref_known(v___x_948_, 1);
if (lean_obj_tag(v_val_949_) == 3)
{
lean_object* v_v_950_; 
v_v_950_ = lean_ctor_get(v_val_949_, 0);
lean_inc(v_v_950_);
lean_dec_ref_known(v_val_949_, 1);
return v_v_950_;
}
else
{
lean_dec(v_val_949_);
lean_inc(v_defValue_946_);
return v_defValue_946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8___boxed(lean_object* v_opts_951_, lean_object* v_opt_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_951_, v_opt_952_);
lean_dec_ref(v_opt_952_);
lean_dec_ref(v_opts_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(size_t v_sz_954_, size_t v_i_955_, lean_object* v_bs_956_){
_start:
{
uint8_t v___x_957_; 
v___x_957_ = lean_usize_dec_lt(v_i_955_, v_sz_954_);
if (v___x_957_ == 0)
{
return v_bs_956_;
}
else
{
lean_object* v_v_958_; lean_object* v_msg_959_; lean_object* v___x_960_; lean_object* v_bs_x27_961_; size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v_v_958_ = lean_array_uget_borrowed(v_bs_956_, v_i_955_);
v_msg_959_ = lean_ctor_get(v_v_958_, 1);
lean_inc_ref(v_msg_959_);
v___x_960_ = lean_unsigned_to_nat(0u);
v_bs_x27_961_ = lean_array_uset(v_bs_956_, v_i_955_, v___x_960_);
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_955_, v___x_962_);
v___x_964_ = lean_array_uset(v_bs_x27_961_, v_i_955_, v_msg_959_);
v_i_955_ = v___x_963_;
v_bs_956_ = v___x_964_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_966_, lean_object* v_i_967_, lean_object* v_bs_968_){
_start:
{
size_t v_sz_boxed_969_; size_t v_i_boxed_970_; lean_object* v_res_971_; 
v_sz_boxed_969_ = lean_unbox_usize(v_sz_966_);
lean_dec(v_sz_966_);
v_i_boxed_970_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_boxed_969_, v_i_boxed_970_, v_bs_968_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object* v_oldTraces_972_, lean_object* v_data_973_, lean_object* v_ref_974_, lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_toCold_981_; lean_object* v_currRecDepth_982_; lean_object* v_ref_983_; uint16_t v_optionFlags_984_; uint8_t v_suppressElabErrors_985_; uint8_t v_isRecordingDeps_986_; lean_object* v_ref_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_traceState_990_; lean_object* v_traces_991_; lean_object* v___x_992_; size_t v_sz_993_; size_t v___x_994_; lean_object* v___x_995_; lean_object* v_msg_996_; lean_object* v___x_997_; lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1036_; 
v_toCold_981_ = lean_ctor_get(v___y_978_, 0);
v_currRecDepth_982_ = lean_ctor_get(v___y_978_, 1);
v_ref_983_ = lean_ctor_get(v___y_978_, 2);
v_optionFlags_984_ = lean_ctor_get_uint16(v___y_978_, sizeof(void*)*3);
v_suppressElabErrors_985_ = lean_ctor_get_uint8(v___y_978_, sizeof(void*)*3 + 2);
v_isRecordingDeps_986_ = lean_ctor_get_uint8(v___y_978_, sizeof(void*)*3 + 3);
v_ref_987_ = l_Lean_replaceRef(v_ref_974_, v_ref_983_);
lean_inc(v_currRecDepth_982_);
lean_inc_ref(v_toCold_981_);
v___x_988_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_988_, 0, v_toCold_981_);
lean_ctor_set(v___x_988_, 1, v_currRecDepth_982_);
lean_ctor_set(v___x_988_, 2, v_ref_987_);
lean_ctor_set_uint16(v___x_988_, sizeof(void*)*3, v_optionFlags_984_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*3 + 2, v_suppressElabErrors_985_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*3 + 3, v_isRecordingDeps_986_);
v___x_989_ = lean_st_ref_get(v___y_979_);
v_traceState_990_ = lean_ctor_get(v___x_989_, 4);
lean_inc_ref(v_traceState_990_);
lean_dec(v___x_989_);
v_traces_991_ = lean_ctor_get(v_traceState_990_, 0);
lean_inc_ref(v_traces_991_);
lean_dec_ref(v_traceState_990_);
v___x_992_ = l_Lean_PersistentArray_toArray___redArg(v_traces_991_);
lean_dec_ref(v_traces_991_);
v_sz_993_ = lean_array_size(v___x_992_);
v___x_994_ = ((size_t)0ULL);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_993_, v___x_994_, v___x_992_);
v_msg_996_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_996_, 0, v_data_973_);
lean_ctor_set(v_msg_996_, 1, v_msg_975_);
lean_ctor_set(v_msg_996_, 2, v___x_995_);
v___x_997_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_996_, v___y_976_, v___y_977_, v___x_988_, v___y_979_);
lean_dec_ref_known(v___x_988_, 3);
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1036_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1036_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v_traceState_1003_; lean_object* v_env_1004_; lean_object* v_nextMacroScope_1005_; lean_object* v_ngen_1006_; lean_object* v_auxDeclNGen_1007_; lean_object* v_cache_1008_; lean_object* v_recordedDeps_1009_; lean_object* v_messages_1010_; lean_object* v_infoState_1011_; lean_object* v_snapshotTasks_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1035_; 
v___x_1002_ = lean_st_ref_take(v___y_979_);
v_traceState_1003_ = lean_ctor_get(v___x_1002_, 4);
v_env_1004_ = lean_ctor_get(v___x_1002_, 0);
v_nextMacroScope_1005_ = lean_ctor_get(v___x_1002_, 1);
v_ngen_1006_ = lean_ctor_get(v___x_1002_, 2);
v_auxDeclNGen_1007_ = lean_ctor_get(v___x_1002_, 3);
v_cache_1008_ = lean_ctor_get(v___x_1002_, 5);
v_recordedDeps_1009_ = lean_ctor_get(v___x_1002_, 6);
v_messages_1010_ = lean_ctor_get(v___x_1002_, 7);
v_infoState_1011_ = lean_ctor_get(v___x_1002_, 8);
v_snapshotTasks_1012_ = lean_ctor_get(v___x_1002_, 9);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1014_ = v___x_1002_;
v_isShared_1015_ = v_isSharedCheck_1035_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_snapshotTasks_1012_);
lean_inc(v_infoState_1011_);
lean_inc(v_messages_1010_);
lean_inc(v_recordedDeps_1009_);
lean_inc(v_cache_1008_);
lean_inc(v_traceState_1003_);
lean_inc(v_auxDeclNGen_1007_);
lean_inc(v_ngen_1006_);
lean_inc(v_nextMacroScope_1005_);
lean_inc(v_env_1004_);
lean_dec(v___x_1002_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1035_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
uint64_t v_tid_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1033_; 
v_tid_1016_ = lean_ctor_get_uint64(v_traceState_1003_, sizeof(void*)*1);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_traceState_1003_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v_traceState_1003_, 0);
lean_dec(v_unused_1034_);
v___x_1018_ = v_traceState_1003_;
v_isShared_1019_ = v_isSharedCheck_1033_;
goto v_resetjp_1017_;
}
else
{
lean_dec(v_traceState_1003_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1033_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1020_ = lean_box(0);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_ref_974_);
lean_ctor_set(v___x_1021_, 1, v_a_998_);
v___x_1022_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_972_, v___x_1021_);
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 0, v___x_1022_);
v___x_1024_ = v___x_1018_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1022_);
lean_ctor_set_uint64(v_reuseFailAlloc_1032_, sizeof(void*)*1, v_tid_1016_);
v___x_1024_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 4, v___x_1024_);
v___x_1026_ = v___x_1014_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_env_1004_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_nextMacroScope_1005_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v_ngen_1006_);
lean_ctor_set(v_reuseFailAlloc_1031_, 3, v_auxDeclNGen_1007_);
lean_ctor_set(v_reuseFailAlloc_1031_, 4, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1031_, 5, v_cache_1008_);
lean_ctor_set(v_reuseFailAlloc_1031_, 6, v_recordedDeps_1009_);
lean_ctor_set(v_reuseFailAlloc_1031_, 7, v_messages_1010_);
lean_ctor_set(v_reuseFailAlloc_1031_, 8, v_infoState_1011_);
lean_ctor_set(v_reuseFailAlloc_1031_, 9, v_snapshotTasks_1012_);
v___x_1026_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_st_ref_put(v___y_979_, v___x_1026_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1020_);
v___x_1029_ = v___x_1000_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1020_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object* v_oldTraces_1037_, lean_object* v_data_1038_, lean_object* v_ref_1039_, lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1037_, v_data_1038_, v_ref_1039_, v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
v_a_1049_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v_x_1047_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v_x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v_x_1047_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v_x_1047_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set_tag(v___x_1059_, 0);
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg___boxed(lean_object* v_x_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object* v_e_1068_){
_start:
{
if (lean_obj_tag(v_e_1068_) == 0)
{
uint8_t v___x_1069_; 
v___x_1069_ = 2;
return v___x_1069_;
}
else
{
uint8_t v___x_1070_; 
v___x_1070_ = 0;
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object* v_e_1071_){
_start:
{
uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_res_1072_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_e_1071_);
lean_dec_ref(v_e_1071_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1077_; double v___x_1078_; 
v___x_1077_ = lean_unsigned_to_nat(1000u);
v___x_1078_ = lean_float_of_nat(v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_cls_1079_, uint8_t v_collapsed_1080_, lean_object* v_tag_1081_, lean_object* v_opts_1082_, uint8_t v_clsEnabled_1083_, lean_object* v_oldTraces_1084_, lean_object* v_msg_1085_, lean_object* v_resStartStop_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_fst_1092_; lean_object* v_snd_1093_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v_data_1097_; lean_object* v_fst_1100_; lean_object* v_snd_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___y_1105_; lean_object* v_a_1106_; uint8_t v___y_1121_; double v___y_1153_; 
v_fst_1092_ = lean_ctor_get(v_resStartStop_1086_, 0);
lean_inc(v_fst_1092_);
v_snd_1093_ = lean_ctor_get(v_resStartStop_1086_, 1);
lean_inc(v_snd_1093_);
lean_dec_ref(v_resStartStop_1086_);
v_fst_1100_ = lean_ctor_get(v_snd_1093_, 0);
lean_inc(v_fst_1100_);
v_snd_1101_ = lean_ctor_get(v_snd_1093_, 1);
lean_inc(v_snd_1101_);
lean_dec(v_snd_1093_);
v___x_1102_ = l_Lean_trace_profiler;
v___x_1103_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1082_, v___x_1102_);
if (v___x_1103_ == 0)
{
v___y_1121_ = v___x_1103_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1158_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1159_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1082_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; double v___x_1162_; double v___x_1163_; double v___x_1164_; 
v___x_1160_ = l_Lean_trace_profiler_threshold;
v___x_1161_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1082_, v___x_1160_);
v___x_1162_ = lean_float_of_nat(v___x_1161_);
v___x_1163_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_1164_ = lean_float_div(v___x_1162_, v___x_1163_);
v___y_1153_ = v___x_1164_;
goto v___jp_1152_;
}
else
{
lean_object* v___x_1165_; lean_object* v___x_1166_; double v___x_1167_; 
v___x_1165_ = l_Lean_trace_profiler_threshold;
v___x_1166_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1082_, v___x_1165_);
v___x_1167_ = lean_float_of_nat(v___x_1166_);
v___y_1153_ = v___x_1167_;
goto v___jp_1152_;
}
}
v___jp_1094_:
{
lean_object* v___x_1098_; 
lean_inc(v___y_1096_);
v___x_1098_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1084_, v_data_1097_, v___y_1096_, v___y_1095_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref_known(v___x_1098_, 1);
v___x_1099_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1092_);
return v___x_1099_;
}
else
{
lean_dec(v_fst_1092_);
return v___x_1098_;
}
}
v___jp_1104_:
{
uint8_t v_result_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; double v___x_1110_; lean_object* v_data_1111_; 
v_result_1107_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_fst_1092_);
v___x_1108_ = lean_box(v_result_1107_);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
v___x_1110_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_1081_);
lean_inc_ref(v___x_1109_);
lean_inc(v_cls_1079_);
v_data_1111_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1111_, 0, v_cls_1079_);
lean_ctor_set(v_data_1111_, 1, v___x_1109_);
lean_ctor_set(v_data_1111_, 2, v_tag_1081_);
lean_ctor_set_float(v_data_1111_, sizeof(void*)*3, v___x_1110_);
lean_ctor_set_float(v_data_1111_, sizeof(void*)*3 + 8, v___x_1110_);
lean_ctor_set_uint8(v_data_1111_, sizeof(void*)*3 + 16, v_collapsed_1080_);
if (v___x_1103_ == 0)
{
lean_dec_ref_known(v___x_1109_, 1);
lean_dec(v_snd_1101_);
lean_dec(v_fst_1100_);
lean_dec_ref(v_tag_1081_);
lean_dec(v_cls_1079_);
v___y_1095_ = v_a_1106_;
v___y_1096_ = v___y_1105_;
v_data_1097_ = v_data_1111_;
goto v___jp_1094_;
}
else
{
lean_object* v_data_1112_; double v___x_1113_; double v___x_1114_; 
lean_dec_ref_known(v_data_1111_, 3);
v_data_1112_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1112_, 0, v_cls_1079_);
lean_ctor_set(v_data_1112_, 1, v___x_1109_);
lean_ctor_set(v_data_1112_, 2, v_tag_1081_);
v___x_1113_ = lean_unbox_float(v_fst_1100_);
lean_dec(v_fst_1100_);
lean_ctor_set_float(v_data_1112_, sizeof(void*)*3, v___x_1113_);
v___x_1114_ = lean_unbox_float(v_snd_1101_);
lean_dec(v_snd_1101_);
lean_ctor_set_float(v_data_1112_, sizeof(void*)*3 + 8, v___x_1114_);
lean_ctor_set_uint8(v_data_1112_, sizeof(void*)*3 + 16, v_collapsed_1080_);
v___y_1095_ = v_a_1106_;
v___y_1096_ = v___y_1105_;
v_data_1097_ = v_data_1112_;
goto v___jp_1094_;
}
}
v___jp_1115_:
{
lean_object* v_ref_1116_; lean_object* v___x_1117_; 
v_ref_1116_ = lean_ctor_get(v___y_1089_, 2);
lean_inc(v___y_1090_);
lean_inc_ref(v___y_1089_);
lean_inc(v___y_1088_);
lean_inc_ref(v___y_1087_);
lean_inc(v_fst_1092_);
v___x_1117_ = lean_apply_6(v_msg_1085_, v_fst_1092_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_, lean_box(0));
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___y_1105_ = v_ref_1116_;
v_a_1106_ = v_a_1118_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1119_; 
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_1105_ = v_ref_1116_;
v_a_1106_ = v___x_1119_;
goto v___jp_1104_;
}
}
v___jp_1120_:
{
if (v_clsEnabled_1083_ == 0)
{
if (v___y_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v_traceState_1123_; lean_object* v_env_1124_; lean_object* v_nextMacroScope_1125_; lean_object* v_ngen_1126_; lean_object* v_auxDeclNGen_1127_; lean_object* v_cache_1128_; lean_object* v_recordedDeps_1129_; lean_object* v_messages_1130_; lean_object* v_infoState_1131_; lean_object* v_snapshotTasks_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_snd_1101_);
lean_dec(v_fst_1100_);
lean_dec_ref(v_msg_1085_);
lean_dec_ref(v_tag_1081_);
lean_dec(v_cls_1079_);
v___x_1122_ = lean_st_ref_take(v___y_1090_);
v_traceState_1123_ = lean_ctor_get(v___x_1122_, 4);
v_env_1124_ = lean_ctor_get(v___x_1122_, 0);
v_nextMacroScope_1125_ = lean_ctor_get(v___x_1122_, 1);
v_ngen_1126_ = lean_ctor_get(v___x_1122_, 2);
v_auxDeclNGen_1127_ = lean_ctor_get(v___x_1122_, 3);
v_cache_1128_ = lean_ctor_get(v___x_1122_, 5);
v_recordedDeps_1129_ = lean_ctor_get(v___x_1122_, 6);
v_messages_1130_ = lean_ctor_get(v___x_1122_, 7);
v_infoState_1131_ = lean_ctor_get(v___x_1122_, 8);
v_snapshotTasks_1132_ = lean_ctor_get(v___x_1122_, 9);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1134_ = v___x_1122_;
v_isShared_1135_ = v_isSharedCheck_1151_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_snapshotTasks_1132_);
lean_inc(v_infoState_1131_);
lean_inc(v_messages_1130_);
lean_inc(v_recordedDeps_1129_);
lean_inc(v_cache_1128_);
lean_inc(v_traceState_1123_);
lean_inc(v_auxDeclNGen_1127_);
lean_inc(v_ngen_1126_);
lean_inc(v_nextMacroScope_1125_);
lean_inc(v_env_1124_);
lean_dec(v___x_1122_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1151_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
uint64_t v_tid_1136_; lean_object* v_traces_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1150_; 
v_tid_1136_ = lean_ctor_get_uint64(v_traceState_1123_, sizeof(void*)*1);
v_traces_1137_ = lean_ctor_get(v_traceState_1123_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_traceState_1123_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1139_ = v_traceState_1123_;
v_isShared_1140_ = v_isSharedCheck_1150_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_traces_1137_);
lean_dec(v_traceState_1123_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1150_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1084_, v_traces_1137_);
lean_dec_ref(v_traces_1137_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1141_);
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1141_);
lean_ctor_set_uint64(v_reuseFailAlloc_1149_, sizeof(void*)*1, v_tid_1136_);
v___x_1143_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1145_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v___x_1143_);
v___x_1145_ = v___x_1134_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_env_1124_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_nextMacroScope_1125_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_ngen_1126_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_auxDeclNGen_1127_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1148_, 5, v_cache_1128_);
lean_ctor_set(v_reuseFailAlloc_1148_, 6, v_recordedDeps_1129_);
lean_ctor_set(v_reuseFailAlloc_1148_, 7, v_messages_1130_);
lean_ctor_set(v_reuseFailAlloc_1148_, 8, v_infoState_1131_);
lean_ctor_set(v_reuseFailAlloc_1148_, 9, v_snapshotTasks_1132_);
v___x_1145_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_st_ref_put(v___y_1090_, v___x_1145_);
v___x_1147_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1092_);
return v___x_1147_;
}
}
}
}
}
else
{
goto v___jp_1115_;
}
}
else
{
goto v___jp_1115_;
}
}
v___jp_1152_:
{
double v___x_1154_; double v___x_1155_; double v___x_1156_; uint8_t v___x_1157_; 
v___x_1154_ = lean_unbox_float(v_snd_1101_);
v___x_1155_ = lean_unbox_float(v_fst_1100_);
v___x_1156_ = lean_float_sub(v___x_1154_, v___x_1155_);
v___x_1157_ = lean_float_decLt(v___y_1153_, v___x_1156_);
v___y_1121_ = v___x_1157_;
goto v___jp_1120_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_cls_1168_, lean_object* v_collapsed_1169_, lean_object* v_tag_1170_, lean_object* v_opts_1171_, lean_object* v_clsEnabled_1172_, lean_object* v_oldTraces_1173_, lean_object* v_msg_1174_, lean_object* v_resStartStop_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v_collapsed_boxed_1181_; uint8_t v_clsEnabled_boxed_1182_; lean_object* v_res_1183_; 
v_collapsed_boxed_1181_ = lean_unbox(v_collapsed_1169_);
v_clsEnabled_boxed_1182_ = lean_unbox(v_clsEnabled_1172_);
v_res_1183_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1168_, v_collapsed_boxed_1181_, v_tag_1170_, v_opts_1171_, v_clsEnabled_boxed_1182_, v_oldTraces_1173_, v_msg_1174_, v_resStartStop_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec_ref(v_opts_1171_);
return v_res_1183_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1186_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = lean_unsigned_to_nat(16u);
v___x_1191_ = lean_mk_array(v___x_1190_, v___x_1189_);
return v___x_1191_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v___x_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; lean_object* v___x_1198_; 
v___x_1195_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1196_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1197_ = 1;
v___x_1198_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1195_);
lean_ctor_set_uint8(v___x_1198_, sizeof(void*)*2, v___x_1197_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(32u);
v___x_1200_ = lean_mk_empty_array_with_capacity(v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
size_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1202_ = ((size_t)5ULL);
v___x_1203_ = lean_unsigned_to_nat(0u);
v___x_1204_ = lean_unsigned_to_nat(32u);
v___x_1205_ = lean_mk_empty_array_with_capacity(v___x_1204_);
v___x_1206_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7);
v___x_1207_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
lean_ctor_set(v___x_1207_, 1, v___x_1205_);
lean_ctor_set(v___x_1207_, 2, v___x_1203_);
lean_ctor_set(v___x_1207_, 3, v___x_1203_);
lean_ctor_set_usize(v___x_1207_, 4, v___x_1202_);
return v___x_1207_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1209_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
lean_ctor_set(v___x_1210_, 2, v___x_1209_);
lean_ctor_set(v___x_1210_, 3, v___x_1208_);
return v___x_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_unsigned_to_nat(0u);
v___x_1212_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1211_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9);
v___x_1215_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_declName_1217_, lean_object* v_as_1218_, size_t v_i_1219_, size_t v_stop_1220_, lean_object* v_b_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_usize_dec_eq(v_i_1219_, v_stop_1220_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_array_uget_borrowed(v_as_1218_, v_i_1219_);
lean_inc(v___x_1228_);
lean_inc(v_declName_1217_);
v___x_1229_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1217_, v___x_1228_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; size_t v___x_1231_; size_t v___x_1232_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = ((size_t)1ULL);
v___x_1232_ = lean_usize_add(v_i_1219_, v___x_1231_);
v_i_1219_ = v___x_1232_;
v_b_1221_ = v_a_1230_;
goto _start;
}
else
{
lean_dec(v_declName_1217_);
return v___x_1229_;
}
}
else
{
lean_object* v___x_1234_; 
lean_dec(v_declName_1217_);
v___x_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1234_, 0, v_b_1221_);
return v___x_1234_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1237_ = l_Lean_stringToMessageData(v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v_cls_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_cls_1250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1251_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_1252_ = l_Lean_Name_append(v___x_1251_, v_cls_1250_);
return v___x_1252_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1253_; double v___x_1254_; 
v___x_1253_ = lean_unsigned_to_nat(1000000000u);
v___x_1254_ = lean_float_of_nat(v___x_1253_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1257_ = l_Lean_stringToMessageData(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1266_ = l_Lean_stringToMessageData(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1269_ = l_Lean_stringToMessageData(v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1270_, lean_object* v___x_1271_, lean_object* v_declName_1272_, lean_object* v_____r_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v___x_1279_ = lean_array_get_size(v_val_1270_);
v___x_1280_ = lean_box(0);
v___x_1281_ = lean_nat_dec_lt(v___x_1271_, v___x_1279_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_declName_1272_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
return v___x_1282_;
}
else
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((size_t)0ULL);
v___x_1284_ = lean_usize_of_nat(v___x_1279_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1272_, v_val_1270_, v___x_1283_, v___x_1284_, v___x_1280_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1285_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1301_, lean_object* v_mvarId_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_toCold_1314_; lean_object* v_options_1315_; uint8_t v_hasTrace_1316_; 
v_toCold_1314_ = lean_ctor_get(v_a_1305_, 0);
v_options_1315_ = lean_ctor_get(v_toCold_1314_, 2);
v_hasTrace_1316_ = lean_ctor_get_uint8(v_options_1315_, sizeof(void*)*1);
if (v_hasTrace_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_inc(v_mvarId_1302_);
v___x_1317_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1494_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1494_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1494_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint8_t v___x_1322_; 
v___x_1322_ = lean_unbox(v_a_1318_);
lean_dec(v_a_1318_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; lean_object* v___x_1324_; 
lean_del_object(v___x_1320_);
v___x_1323_ = 1;
lean_inc(v_mvarId_1302_);
v___x_1324_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1481_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1481_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1481_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_unbox(v_a_1325_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_del_object(v___x_1327_);
lean_inc(v_mvarId_1302_);
v___x_1330_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
if (lean_obj_tag(v_a_1331_) == 1)
{
lean_object* v_val_1332_; 
lean_dec(v_a_1325_);
lean_dec(v_mvarId_1302_);
v_val_1332_ = lean_ctor_get(v_a_1331_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_a_1331_, 1);
v_mvarId_1302_ = v_val_1332_;
goto _start;
}
else
{
lean_object* v___x_1334_; 
lean_dec(v_a_1331_);
lean_inc(v_mvarId_1302_);
v___x_1334_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc(v_a_1335_);
lean_dec_ref_known(v___x_1334_, 1);
if (lean_obj_tag(v_a_1335_) == 1)
{
lean_object* v_val_1336_; 
lean_dec(v_a_1325_);
lean_dec(v_mvarId_1302_);
v_val_1336_ = lean_ctor_get(v_a_1335_, 0);
lean_inc(v_val_1336_);
lean_dec_ref_known(v_a_1335_, 1);
v_mvarId_1302_ = v_val_1336_;
goto _start;
}
else
{
lean_object* v___x_1338_; 
lean_dec(v_a_1335_);
lean_inc(v_mvarId_1302_);
v___x_1338_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1302_, v___x_1323_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
if (lean_obj_tag(v_a_1339_) == 1)
{
lean_object* v_val_1340_; 
lean_dec(v_a_1325_);
lean_dec(v_mvarId_1302_);
v_val_1340_ = lean_ctor_get(v_a_1339_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v_a_1339_, 1);
v_mvarId_1302_ = v_val_1340_;
goto _start;
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; uint8_t v___x_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; uint8_t v___x_1351_; uint8_t v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; uint8_t v___x_1356_; uint8_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
lean_dec(v_a_1339_);
v___x_1342_ = lean_unsigned_to_nat(100000u);
v___x_1343_ = lean_unsigned_to_nat(2u);
v___x_1344_ = 0;
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1346_, 0, v___x_1342_);
lean_ctor_set(v___x_1346_, 1, v___x_1343_);
lean_ctor_set(v___x_1346_, 2, v___x_1345_);
v___x_1347_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3, v___x_1347_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 1, v___x_1323_);
v___x_1348_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 2, v___x_1348_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 3, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 4, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 5, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 6, v___x_1344_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 7, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 8, v___x_1323_);
v___x_1349_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 9, v___x_1349_);
v___x_1350_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 10, v___x_1350_);
v___x_1351_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 11, v___x_1351_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 12, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 13, v___x_1323_);
v___x_1352_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 14, v___x_1352_);
v___x_1353_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 15, v___x_1353_);
v___x_1354_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 16, v___x_1354_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 17, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 18, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 19, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 20, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 21, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 22, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 23, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 24, v___x_1323_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 25, v___x_1323_);
v___x_1355_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 26, v___x_1355_);
v___x_1356_ = lean_unbox(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 27, v___x_1356_);
v___x_1357_ = lean_unbox(v_a_1325_);
lean_dec(v_a_1325_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*3 + 28, v___x_1357_);
v___x_1358_ = lean_unsigned_to_nat(0u);
v___x_1359_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1360_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1361_ = l_Lean_Options_empty;
v___x_1362_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1346_, v___x_1359_, v___x_1360_, v___x_1361_, v_a_1303_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v___x_1364_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1302_);
v___x_1365_ = l_Lean_Meta_simpTargetStar(v_mvarId_1302_, v_a_1363_, v___x_1359_, v___x_1345_, v___x_1364_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1436_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1436_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1436_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_fst_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1434_; 
v_fst_1370_ = lean_ctor_get(v_a_1366_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_a_1366_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; 
v_unused_1435_ = lean_ctor_get(v_a_1366_, 1);
lean_dec(v_unused_1435_);
v___x_1372_ = v_a_1366_;
v_isShared_1373_ = v_isSharedCheck_1434_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_fst_1370_);
lean_dec(v_a_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1434_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
switch(lean_obj_tag(v_fst_1370_))
{
case 0:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_del_object(v___x_1372_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v___x_1374_ = lean_box(0);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1374_);
v___x_1376_ = v___x_1368_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
case 1:
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1368_);
lean_inc(v_declName_1301_);
lean_inc(v_mvarId_1302_);
v___x_1378_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1302_, v_declName_1301_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
if (lean_obj_tag(v_a_1379_) == 1)
{
lean_object* v_val_1380_; 
lean_del_object(v___x_1372_);
lean_dec(v_mvarId_1302_);
v_val_1380_ = lean_ctor_get(v_a_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_a_1379_, 1);
v_mvarId_1302_ = v_val_1380_;
goto _start;
}
else
{
lean_object* v___x_1382_; 
lean_dec(v_a_1379_);
lean_inc(v_mvarId_1302_);
v___x_1382_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1415_; 
v_a_1383_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1385_ = v___x_1382_;
v_isShared_1386_ = v_isSharedCheck_1415_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1382_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1415_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
if (lean_obj_tag(v_a_1383_) == 1)
{
lean_object* v_val_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
lean_del_object(v___x_1372_);
lean_dec(v_mvarId_1302_);
v_val_1387_ = lean_ctor_get(v_a_1383_, 0);
lean_inc(v_val_1387_);
lean_dec_ref_known(v_a_1383_, 1);
v___x_1388_ = lean_array_get_size(v_val_1387_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_nat_dec_lt(v___x_1358_, v___x_1388_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1392_; 
lean_dec(v_val_1387_);
lean_dec(v_declName_1301_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v___x_1389_);
v___x_1392_ = v___x_1385_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1389_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
else
{
size_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
lean_del_object(v___x_1385_);
v___x_1394_ = ((size_t)0ULL);
v___x_1395_ = lean_usize_of_nat(v___x_1388_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1301_, v_val_1387_, v___x_1394_, v___x_1395_, v___x_1389_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_val_1387_);
return v___x_1396_;
}
}
else
{
lean_object* v___x_1397_; 
lean_del_object(v___x_1385_);
lean_dec(v_a_1383_);
lean_inc(v_mvarId_1302_);
v___x_1397_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1302_, v___x_1323_, v___x_1323_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1399_; lean_object* v___x_1400_; 
lean_del_object(v___x_1372_);
lean_dec(v_mvarId_1302_);
v_val_1399_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1399_);
lean_dec_ref_known(v_a_1398_, 1);
v___x_1400_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1301_, v_val_1399_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1400_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
lean_dec(v_a_1398_);
lean_dec(v_declName_1301_);
v___x_1401_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v_mvarId_1302_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set_tag(v___x_1372_, 7);
lean_ctor_set(v___x_1372_, 1, v___x_1402_);
lean_ctor_set(v___x_1372_, 0, v___x_1401_);
v___x_1404_ = v___x_1372_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1404_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1405_;
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_del_object(v___x_1372_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1407_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1397_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1397_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_del_object(v___x_1372_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1416_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1382_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1382_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_del_object(v___x_1372_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1424_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1378_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1378_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1432_; 
lean_del_object(v___x_1372_);
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1302_);
v_mvarId_1432_ = lean_ctor_get(v_fst_1370_, 0);
lean_inc(v_mvarId_1432_);
lean_dec_ref_known(v_fst_1370_, 1);
v_mvarId_1302_ = v_mvarId_1432_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1437_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1365_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1365_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1445_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1362_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1362_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
else
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
lean_dec(v_a_1325_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1453_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1338_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1338_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_a_1325_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1461_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1334_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1334_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_a_1325_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1469_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1330_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1330_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_dec(v_a_1325_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v___x_1477_ = lean_box(0);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1477_);
v___x_1479_ = v___x_1327_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
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
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1482_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1324_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1324_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
else
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v___x_1490_ = lean_box(0);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1490_);
v___x_1492_ = v___x_1320_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
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
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1495_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1317_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1317_);
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
else
{
lean_object* v_inheritedTraceOptions_1503_; lean_object* v___f_1504_; lean_object* v_cls_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; uint8_t v___x_1508_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v_a_1512_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_a_1524_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v_a_1529_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v_a_1540_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v_a_1555_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v_a_1560_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; 
v_inheritedTraceOptions_1503_ = lean_ctor_get(v_toCold_1314_, 11);
lean_inc(v_mvarId_1302_);
v___f_1504_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1504_, 0, v_mvarId_1302_);
v_cls_1505_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1506_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1507_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1508_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1503_, v_options_1315_, v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1865_; uint8_t v___x_1866_; 
v___x_1865_ = l_Lean_trace_profiler;
v___x_1866_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1315_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec_ref(v___f_1504_);
lean_inc(v_mvarId_1302_);
v___x_1867_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; uint8_t v___x_1869_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = lean_unbox(v_a_1868_);
lean_dec(v_a_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
lean_inc(v_mvarId_1302_);
v___x_1870_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; uint8_t v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = lean_unbox(v_a_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_inc(v_mvarId_1302_);
v___x_1873_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
if (lean_obj_tag(v_a_1874_) == 1)
{
lean_dec(v_a_1871_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1875_; 
v_val_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_val_1875_);
lean_dec_ref_known(v_a_1874_, 1);
v_mvarId_1302_ = v_val_1875_;
goto _start;
}
else
{
lean_object* v_val_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v_val_1877_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v_a_1874_, 1);
v___x_1878_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1879_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1878_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_dec_ref_known(v___x_1879_, 1);
v_mvarId_1302_ = v_val_1877_;
goto _start;
}
else
{
lean_dec(v_val_1877_);
lean_dec(v_declName_1301_);
return v___x_1879_;
}
}
}
else
{
lean_object* v___x_1881_; 
lean_dec(v_a_1874_);
lean_inc(v_mvarId_1302_);
v___x_1881_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
if (lean_obj_tag(v_a_1882_) == 1)
{
lean_dec(v_a_1871_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1883_; 
v_val_1883_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_val_1883_);
lean_dec_ref_known(v_a_1882_, 1);
v_mvarId_1302_ = v_val_1883_;
goto _start;
}
else
{
lean_object* v_val_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
v_val_1885_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v_a_1882_, 1);
v___x_1886_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1887_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1886_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_dec_ref_known(v___x_1887_, 1);
v_mvarId_1302_ = v_val_1885_;
goto _start;
}
else
{
lean_dec(v_val_1885_);
lean_dec(v_declName_1301_);
return v___x_1887_;
}
}
}
else
{
lean_object* v___x_1889_; 
lean_dec(v_a_1882_);
lean_inc(v_mvarId_1302_);
v___x_1889_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1302_, v_hasTrace_1316_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
if (lean_obj_tag(v_a_1890_) == 1)
{
lean_dec(v_a_1871_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1891_; 
v_val_1891_ = lean_ctor_get(v_a_1890_, 0);
lean_inc(v_val_1891_);
lean_dec_ref_known(v_a_1890_, 1);
v_mvarId_1302_ = v_val_1891_;
goto _start;
}
else
{
lean_object* v_val_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_val_1893_ = lean_ctor_get(v_a_1890_, 0);
lean_inc(v_val_1893_);
lean_dec_ref_known(v_a_1890_, 1);
v___x_1894_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1895_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1894_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_dec_ref_known(v___x_1895_, 1);
v_mvarId_1302_ = v_val_1893_;
goto _start;
}
else
{
lean_dec(v_val_1893_);
lean_dec(v_declName_1301_);
return v___x_1895_;
}
}
}
else
{
lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; uint8_t v___x_1903_; uint8_t v___x_1904_; uint8_t v___x_1905_; uint8_t v___x_1906_; uint8_t v___x_1907_; uint8_t v___x_1908_; uint8_t v___x_1909_; uint8_t v___x_1910_; uint8_t v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_dec(v_a_1890_);
v___x_1897_ = lean_unsigned_to_nat(100000u);
v___x_1898_ = lean_unsigned_to_nat(2u);
v___x_1899_ = 0;
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1901_, 0, v___x_1897_);
lean_ctor_set(v___x_1901_, 1, v___x_1898_);
lean_ctor_set(v___x_1901_, 2, v___x_1900_);
v___x_1902_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3, v___x_1902_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 1, v_hasTrace_1316_);
v___x_1903_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 2, v___x_1903_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 3, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 4, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 5, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 6, v___x_1899_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 7, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 8, v_hasTrace_1316_);
v___x_1904_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 9, v___x_1904_);
v___x_1905_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 10, v___x_1905_);
v___x_1906_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 11, v___x_1906_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 12, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 13, v_hasTrace_1316_);
v___x_1907_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 14, v___x_1907_);
v___x_1908_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 15, v___x_1908_);
v___x_1909_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 16, v___x_1909_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 17, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 18, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 19, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 20, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 21, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 22, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 23, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 24, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 25, v_hasTrace_1316_);
v___x_1910_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 26, v___x_1910_);
v___x_1911_ = lean_unbox(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 27, v___x_1911_);
v___x_1912_ = lean_unbox(v_a_1871_);
lean_dec(v_a_1871_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*3 + 28, v___x_1912_);
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1916_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1917_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
lean_ctor_set_uint8(v___x_1917_, sizeof(void*)*2, v_hasTrace_1316_);
v___x_1918_ = l_Lean_Options_empty;
v___x_1919_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1901_, v___x_1914_, v___x_1917_, v___x_1918_, v_a_1303_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v_a_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref_known(v___x_1919_, 1);
v___x_1921_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1302_);
v___x_1922_ = l_Lean_Meta_simpTargetStar(v_mvarId_1302_, v_a_1920_, v___x_1914_, v___x_1900_, v___x_1921_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_2014_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_2014_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_2014_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_2014_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v_fst_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_2012_; 
v_fst_1927_ = lean_ctor_get(v_a_1923_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_a_1923_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v_a_1923_, 1);
lean_dec(v_unused_2013_);
v___x_1929_ = v_a_1923_;
v_isShared_1930_ = v_isSharedCheck_2012_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_fst_1927_);
lean_dec(v_a_1923_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_2012_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
switch(lean_obj_tag(v_fst_1927_))
{
case 0:
{
lean_del_object(v___x_1929_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = lean_box(0);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1931_);
v___x_1933_ = v___x_1925_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
lean_del_object(v___x_1925_);
v___x_1935_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1936_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1935_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1936_;
}
}
case 1:
{
lean_object* v___x_1937_; 
lean_del_object(v___x_1925_);
lean_inc(v_declName_1301_);
lean_inc(v_mvarId_1302_);
v___x_1937_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1302_, v_declName_1301_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
if (lean_obj_tag(v_a_1938_) == 1)
{
lean_del_object(v___x_1929_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1939_; 
v_val_1939_ = lean_ctor_get(v_a_1938_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v_a_1938_, 1);
v_mvarId_1302_ = v_val_1939_;
goto _start;
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_val_1941_ = lean_ctor_get(v_a_1938_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_a_1938_, 1);
v___x_1942_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1943_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1942_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_dec_ref_known(v___x_1943_, 1);
v_mvarId_1302_ = v_val_1941_;
goto _start;
}
else
{
lean_dec(v_val_1941_);
lean_dec(v_declName_1301_);
return v___x_1943_;
}
}
}
else
{
lean_object* v___x_1945_; 
lean_dec(v_a_1938_);
lean_inc(v_mvarId_1302_);
v___x_1945_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1989_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1989_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1989_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
if (lean_obj_tag(v_a_1946_) == 1)
{
lean_object* v_val_1950_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; 
lean_del_object(v___x_1929_);
lean_dec(v_mvarId_1302_);
v_val_1950_ = lean_ctor_get(v_a_1946_, 0);
lean_inc(v_val_1950_);
lean_dec_ref_known(v_a_1946_, 1);
if (v___x_1508_ == 0)
{
v___y_1952_ = v_a_1303_;
v___y_1953_ = v_a_1304_;
v___y_1954_ = v_a_1305_;
v___y_1955_ = v_a_1306_;
goto v___jp_1951_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1966_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1965_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_dec_ref_known(v___x_1966_, 1);
v___y_1952_ = v_a_1303_;
v___y_1953_ = v_a_1304_;
v___y_1954_ = v_a_1305_;
v___y_1955_ = v_a_1306_;
goto v___jp_1951_;
}
else
{
lean_dec(v_val_1950_);
lean_del_object(v___x_1948_);
lean_dec(v_declName_1301_);
return v___x_1966_;
}
}
v___jp_1951_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1956_ = lean_array_get_size(v_val_1950_);
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_nat_dec_lt(v___x_1913_, v___x_1956_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1960_; 
lean_dec(v_val_1950_);
lean_dec(v_declName_1301_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1957_);
v___x_1960_ = v___x_1948_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1957_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
else
{
size_t v___x_1962_; size_t v___x_1963_; lean_object* v___x_1964_; 
lean_del_object(v___x_1948_);
v___x_1962_ = ((size_t)0ULL);
v___x_1963_ = lean_usize_of_nat(v___x_1956_);
v___x_1964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1301_, v_val_1950_, v___x_1962_, v___x_1963_, v___x_1957_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v_val_1950_);
return v___x_1964_;
}
}
}
else
{
lean_object* v___x_1967_; 
lean_del_object(v___x_1948_);
lean_dec(v_a_1946_);
lean_inc(v_mvarId_1302_);
v___x_1967_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1302_, v_hasTrace_1316_, v_hasTrace_1316_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
if (lean_obj_tag(v_a_1968_) == 1)
{
lean_del_object(v___x_1929_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1969_; lean_object* v___x_1970_; 
v_val_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v_a_1968_, 1);
v___x_1970_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1301_, v_val_1969_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1970_;
}
else
{
lean_object* v_val_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_val_1971_ = lean_ctor_get(v_a_1968_, 0);
lean_inc(v_val_1971_);
lean_dec_ref_known(v_a_1968_, 1);
v___x_1972_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1973_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1972_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref_known(v___x_1973_, 1);
v___x_1974_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1301_, v_val_1971_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1974_;
}
else
{
lean_dec(v_val_1971_);
lean_dec(v_declName_1301_);
return v___x_1973_;
}
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec(v_a_1968_);
lean_dec(v_declName_1301_);
v___x_1975_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v_mvarId_1302_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set_tag(v___x_1929_, 7);
lean_ctor_set(v___x_1929_, 1, v___x_1976_);
lean_ctor_set(v___x_1929_, 0, v___x_1975_);
v___x_1978_ = v___x_1929_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1978_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1979_;
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_del_object(v___x_1929_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1981_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1967_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1967_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
lean_del_object(v___x_1929_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1990_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1945_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1945_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
else
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2005_; 
lean_del_object(v___x_1929_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1998_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_2000_ = v___x_1937_;
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1937_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2005_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2003_; 
if (v_isShared_2001_ == 0)
{
v___x_2003_ = v___x_2000_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
default: 
{
lean_del_object(v___x_1929_);
lean_del_object(v___x_1925_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_mvarId_2006_; 
v_mvarId_2006_ = lean_ctor_get(v_fst_1927_, 0);
lean_inc(v_mvarId_2006_);
lean_dec_ref_known(v_fst_1927_, 1);
v_mvarId_1302_ = v_mvarId_2006_;
goto _start;
}
else
{
lean_object* v_mvarId_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_mvarId_2008_ = lean_ctor_get(v_fst_1927_, 0);
lean_inc(v_mvarId_2008_);
lean_dec_ref_known(v_fst_1927_, 1);
v___x_2009_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2010_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_2009_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_dec_ref_known(v___x_2010_, 1);
v_mvarId_1302_ = v_mvarId_2008_;
goto _start;
}
else
{
lean_dec(v_mvarId_2008_);
lean_dec(v_declName_1301_);
return v___x_2010_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_2015_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_1922_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_1922_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_a_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_2023_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1919_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1919_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_a_1871_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_2031_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_1889_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_1889_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_1871_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_2039_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_1881_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_1881_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_1871_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_2047_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_1873_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_1873_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_dec(v_a_1871_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
goto v___jp_1311_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2056_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_2055_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_dec_ref_known(v___x_2056_, 1);
goto v___jp_1311_;
}
else
{
return v___x_2056_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_2057_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_1870_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_1870_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
goto v___jp_1308_;
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2066_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_2065_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_dec_ref_known(v___x_2066_, 1);
goto v___jp_1308_;
}
else
{
return v___x_2066_;
}
}
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_2067_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_1867_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_1867_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
goto v___jp_1568_;
}
}
else
{
goto v___jp_1568_;
}
v___jp_1509_:
{
lean_object* v___x_1513_; double v___x_1514_; double v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1513_ = lean_io_get_num_heartbeats();
v___x_1514_ = lean_float_of_nat(v___y_1511_);
v___x_1515_ = lean_float_of_nat(v___x_1513_);
v___x_1516_ = lean_box_float(v___x_1514_);
v___x_1517_ = lean_box_float(v___x_1515_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_a_1512_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1505_, v_hasTrace_1316_, v___x_1506_, v_options_1315_, v___x_1508_, v___y_1510_, v___f_1504_, v___x_1519_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1520_;
}
v___jp_1521_:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1524_);
v___y_1510_ = v___y_1522_;
v___y_1511_ = v___y_1523_;
v_a_1512_ = v___x_1525_;
goto v___jp_1509_;
}
v___jp_1526_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1529_);
v___y_1510_ = v___y_1527_;
v___y_1511_ = v___y_1528_;
v_a_1512_ = v___x_1530_;
goto v___jp_1509_;
}
v___jp_1531_:
{
if (lean_obj_tag(v___y_1534_) == 0)
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___y_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___y_1534_, 1);
v___y_1527_ = v___y_1532_;
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1535_;
goto v___jp_1526_;
}
else
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___y_1534_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___y_1534_, 1);
v___y_1522_ = v___y_1532_;
v___y_1523_ = v___y_1533_;
v_a_1524_ = v_a_1536_;
goto v___jp_1521_;
}
}
v___jp_1537_:
{
lean_object* v___x_1541_; double v___x_1542_; double v___x_1543_; double v___x_1544_; double v___x_1545_; double v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1541_ = lean_io_mono_nanos_now();
v___x_1542_ = lean_float_of_nat(v___y_1539_);
v___x_1543_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1544_ = lean_float_div(v___x_1542_, v___x_1543_);
v___x_1545_ = lean_float_of_nat(v___x_1541_);
v___x_1546_ = lean_float_div(v___x_1545_, v___x_1543_);
v___x_1547_ = lean_box_float(v___x_1544_);
v___x_1548_ = lean_box_float(v___x_1546_);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v_a_1540_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1505_, v_hasTrace_1316_, v___x_1506_, v_options_1315_, v___x_1508_, v___y_1538_, v___f_1504_, v___x_1550_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
return v___x_1551_;
}
v___jp_1552_:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_a_1555_);
v___y_1538_ = v___y_1553_;
v___y_1539_ = v___y_1554_;
v_a_1540_ = v___x_1556_;
goto v___jp_1537_;
}
v___jp_1557_:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_a_1560_);
v___y_1538_ = v___y_1558_;
v___y_1539_ = v___y_1559_;
v_a_1540_ = v___x_1561_;
goto v___jp_1537_;
}
v___jp_1562_:
{
if (lean_obj_tag(v___y_1565_) == 0)
{
lean_object* v_a_1566_; 
v_a_1566_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___y_1565_, 1);
v___y_1553_ = v___y_1563_;
v___y_1554_ = v___y_1564_;
v_a_1555_ = v_a_1566_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1567_; 
v_a_1567_ = lean_ctor_get(v___y_1565_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___y_1565_, 1);
v___y_1558_ = v___y_1563_;
v___y_1559_ = v___y_1564_;
v_a_1560_ = v_a_1567_;
goto v___jp_1557_;
}
}
v___jp_1568_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1306_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v___x_1571_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1572_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1315_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1302_);
v___x_1574_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; uint8_t v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = lean_unbox(v_a_1575_);
lean_dec(v_a_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_inc(v_mvarId_1302_);
v___x_1577_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; uint8_t v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = lean_unbox(v_a_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_inc(v_mvarId_1302_);
v___x_1580_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_dec(v_a_1578_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1582_; lean_object* v___x_1583_; 
v_val_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_a_1581_, 1);
v___x_1583_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1582_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1583_;
goto v___jp_1562_;
}
else
{
lean_object* v_val_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_val_1584_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1584_);
lean_dec_ref_known(v_a_1581_, 1);
v___x_1585_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1586_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1585_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref_known(v___x_1586_, 1);
v___x_1587_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1584_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1587_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1588_; 
lean_dec(v_val_1584_);
lean_dec(v_declName_1301_);
v_a_1588_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1586_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1588_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1589_; 
lean_dec(v_a_1581_);
lean_inc(v_mvarId_1302_);
v___x_1589_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
if (lean_obj_tag(v_a_1590_) == 1)
{
lean_dec(v_a_1578_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1591_; lean_object* v___x_1592_; 
v_val_1591_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v_a_1590_, 1);
v___x_1592_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1591_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1592_;
goto v___jp_1562_;
}
else
{
lean_object* v_val_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_val_1593_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v_a_1590_, 1);
v___x_1594_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1595_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1594_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1596_; 
lean_dec_ref_known(v___x_1595_, 1);
v___x_1596_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1593_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1596_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1597_; 
lean_dec(v_val_1593_);
lean_dec(v_declName_1301_);
v_a_1597_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1595_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1597_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1598_; 
lean_dec(v_a_1590_);
lean_inc(v_mvarId_1302_);
v___x_1598_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1302_, v_hasTrace_1316_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
if (lean_obj_tag(v_a_1599_) == 1)
{
lean_dec(v_a_1578_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1600_; lean_object* v___x_1601_; 
v_val_1600_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_a_1599_, 1);
v___x_1601_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1600_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1601_;
goto v___jp_1562_;
}
else
{
lean_object* v_val_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_val_1602_ = lean_ctor_get(v_a_1599_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v_a_1599_, 1);
v___x_1603_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1604_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1603_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref_known(v___x_1604_, 1);
v___x_1605_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1602_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1605_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1606_; 
lean_dec(v_val_1602_);
lean_dec(v_declName_1301_);
v_a_1606_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1604_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1606_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; uint8_t v___x_1613_; uint8_t v___x_1614_; uint8_t v___x_1615_; uint8_t v___x_1616_; uint8_t v___x_1617_; uint8_t v___x_1618_; uint8_t v___x_1619_; uint8_t v___x_1620_; uint8_t v___x_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
lean_dec(v_a_1599_);
v___x_1607_ = lean_unsigned_to_nat(100000u);
v___x_1608_ = lean_unsigned_to_nat(2u);
v___x_1609_ = 0;
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1611_, 0, v___x_1607_);
lean_ctor_set(v___x_1611_, 1, v___x_1608_);
lean_ctor_set(v___x_1611_, 2, v___x_1610_);
v___x_1612_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3, v___x_1612_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 1, v_hasTrace_1316_);
v___x_1613_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 2, v___x_1613_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 3, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 4, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 5, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 6, v___x_1609_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 7, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 8, v_hasTrace_1316_);
v___x_1614_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 9, v___x_1614_);
v___x_1615_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 10, v___x_1615_);
v___x_1616_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 11, v___x_1616_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 12, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 13, v_hasTrace_1316_);
v___x_1617_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 14, v___x_1617_);
v___x_1618_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 15, v___x_1618_);
v___x_1619_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 16, v___x_1619_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 17, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 18, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 19, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 20, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 21, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 22, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 23, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 24, v_hasTrace_1316_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 25, v_hasTrace_1316_);
v___x_1620_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 26, v___x_1620_);
v___x_1621_ = lean_unbox(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 27, v___x_1621_);
v___x_1622_ = lean_unbox(v_a_1578_);
lean_dec(v_a_1578_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 28, v___x_1622_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1625_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1626_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1627_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*2, v_hasTrace_1316_);
v___x_1628_ = l_Lean_Options_empty;
v___x_1629_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1611_, v___x_1624_, v___x_1627_, v___x_1628_, v_a_1303_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1302_);
v___x_1632_ = l_Lean_Meta_simpTargetStar(v_mvarId_1302_, v_a_1630_, v___x_1624_, v___x_1610_, v___x_1631_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v_fst_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1692_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v___x_1632_, 1);
v_fst_1634_ = lean_ctor_get(v_a_1633_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_a_1633_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v_a_1633_, 1);
lean_dec(v_unused_1693_);
v___x_1636_ = v_a_1633_;
v_isShared_1637_ = v_isSharedCheck_1692_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_fst_1634_);
lean_dec(v_a_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1692_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
switch(lean_obj_tag(v_fst_1634_))
{
case 0:
{
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1638_; 
v___x_1638_ = lean_box(0);
v___y_1553_ = v_a_1570_;
v___y_1554_ = v___x_1573_;
v_a_1555_ = v___x_1638_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1640_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1639_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1640_;
goto v___jp_1562_;
}
}
case 1:
{
lean_object* v___x_1641_; 
lean_inc(v_declName_1301_);
lean_inc(v_mvarId_1302_);
v___x_1641_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1302_, v_declName_1301_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
if (lean_obj_tag(v_a_1642_) == 1)
{
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1643_; lean_object* v___x_1644_; 
v_val_1643_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v_a_1642_, 1);
v___x_1644_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1643_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1644_;
goto v___jp_1562_;
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_val_1645_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v_a_1642_, 1);
v___x_1646_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1647_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1646_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref_known(v___x_1647_, 1);
v___x_1648_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1645_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1648_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1649_; 
lean_dec(v_val_1645_);
lean_dec(v_declName_1301_);
v_a_1649_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1647_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1649_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1650_; 
lean_dec(v_a_1642_);
lean_inc(v_mvarId_1302_);
v___x_1650_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
if (lean_obj_tag(v_a_1651_) == 1)
{
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_val_1652_ = lean_ctor_get(v_a_1651_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v_a_1651_, 1);
v___x_1653_ = lean_box(0);
v___x_1654_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1652_, v___x_1623_, v_declName_1301_, v___x_1653_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_val_1652_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1654_;
goto v___jp_1562_;
}
else
{
lean_object* v_val_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_val_1655_ = lean_ctor_get(v_a_1651_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v_a_1651_, 1);
v___x_1656_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1657_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1656_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1655_, v___x_1623_, v_declName_1301_, v_a_1658_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_val_1655_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1659_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1660_; 
lean_dec(v_val_1655_);
lean_dec(v_declName_1301_);
v_a_1660_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1657_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1660_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1661_; 
lean_dec(v_a_1651_);
lean_inc(v_mvarId_1302_);
v___x_1661_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1302_, v_hasTrace_1316_, v_hasTrace_1316_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1681_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1681_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1681_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
if (lean_obj_tag(v_a_1662_) == 1)
{
lean_del_object(v___x_1664_);
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1666_; lean_object* v___x_1667_; 
v_val_1666_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v_a_1662_, 1);
v___x_1667_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1301_, v_val_1666_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1667_;
goto v___jp_1562_;
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_val_1668_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1668_);
lean_dec_ref_known(v_a_1662_, 1);
v___x_1669_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1670_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1669_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1671_; 
lean_dec_ref_known(v___x_1670_, 1);
v___x_1671_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1301_, v_val_1668_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1671_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1672_; 
lean_dec(v_val_1668_);
lean_dec(v_declName_1301_);
v_a_1672_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1670_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1672_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_dec(v_a_1662_);
lean_dec(v_declName_1301_);
v___x_1673_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 1);
lean_ctor_set(v___x_1664_, 0, v_mvarId_1302_);
v___x_1675_ = v___x_1664_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_mvarId_1302_);
v___x_1675_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set_tag(v___x_1636_, 7);
lean_ctor_set(v___x_1636_, 1, v___x_1675_);
lean_ctor_set(v___x_1636_, 0, v___x_1673_);
v___x_1677_ = v___x_1636_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1677_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1678_;
goto v___jp_1562_;
}
}
}
}
}
else
{
lean_object* v_a_1682_; 
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1682_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1661_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1682_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1683_; 
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1683_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1650_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1683_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1684_; 
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1684_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1641_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1684_;
goto v___jp_1557_;
}
}
default: 
{
lean_del_object(v___x_1636_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_mvarId_1685_; lean_object* v___x_1686_; 
v_mvarId_1685_ = lean_ctor_get(v_fst_1634_, 0);
lean_inc(v_mvarId_1685_);
lean_dec_ref_known(v_fst_1634_, 1);
v___x_1686_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_mvarId_1685_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1686_;
goto v___jp_1562_;
}
else
{
lean_object* v_mvarId_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_mvarId_1687_ = lean_ctor_get(v_fst_1634_, 0);
lean_inc(v_mvarId_1687_);
lean_dec_ref_known(v_fst_1634_, 1);
v___x_1688_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1689_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1688_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref_known(v___x_1689_, 1);
v___x_1690_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_mvarId_1687_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1690_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1691_; 
lean_dec(v_mvarId_1687_);
lean_dec(v_declName_1301_);
v_a_1691_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1689_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1691_;
goto v___jp_1557_;
}
}
}
}
}
}
else
{
lean_object* v_a_1694_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1694_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1632_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1694_;
goto v___jp_1557_;
}
}
else
{
lean_object* v_a_1695_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1695_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1629_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1695_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1696_; 
lean_dec(v_a_1578_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1696_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1598_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1696_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1697_; 
lean_dec(v_a_1578_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1697_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1589_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1697_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v_a_1698_; 
lean_dec(v_a_1578_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1698_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1698_);
lean_dec_ref_known(v___x_1580_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1698_;
goto v___jp_1557_;
}
}
else
{
lean_dec(v_a_1578_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_box(0);
v___x_1700_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1699_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1700_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1702_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1701_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1703_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1704_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1705_; 
v_a_1705_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1702_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1705_;
goto v___jp_1557_;
}
}
}
}
else
{
lean_object* v_a_1706_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1706_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1577_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1706_;
goto v___jp_1557_;
}
}
else
{
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_box(0);
v___x_1708_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1707_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1708_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1710_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1709_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1712_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1711_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1563_ = v_a_1570_;
v___y_1564_ = v___x_1573_;
v___y_1565_ = v___x_1712_;
goto v___jp_1562_;
}
else
{
lean_object* v_a_1713_; 
v_a_1713_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1710_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1713_;
goto v___jp_1557_;
}
}
}
}
else
{
lean_object* v_a_1714_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1714_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1574_, 1);
v___y_1558_ = v_a_1570_;
v___y_1559_ = v___x_1573_;
v_a_1560_ = v_a_1714_;
goto v___jp_1557_;
}
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1302_);
v___x_1716_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; uint8_t v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = lean_unbox(v_a_1717_);
lean_dec(v_a_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; 
lean_inc(v_mvarId_1302_);
v___x_1719_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; uint8_t v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = lean_unbox(v_a_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_inc(v_mvarId_1302_);
v___x_1722_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
if (lean_obj_tag(v_a_1723_) == 1)
{
lean_dec(v_a_1720_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1724_; lean_object* v___x_1725_; 
v_val_1724_ = lean_ctor_get(v_a_1723_, 0);
lean_inc(v_val_1724_);
lean_dec_ref_known(v_a_1723_, 1);
v___x_1725_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1724_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1725_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_val_1726_ = lean_ctor_get(v_a_1723_, 0);
lean_inc(v_val_1726_);
lean_dec_ref_known(v_a_1723_, 1);
v___x_1727_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1728_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1727_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v___x_1729_; 
lean_dec_ref_known(v___x_1728_, 1);
v___x_1729_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1726_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1729_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1730_; 
lean_dec(v_val_1726_);
lean_dec(v_declName_1301_);
v_a_1730_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1728_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1730_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_a_1723_);
lean_inc(v_mvarId_1302_);
v___x_1731_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
if (lean_obj_tag(v_a_1732_) == 1)
{
lean_dec(v_a_1720_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1733_; lean_object* v___x_1734_; 
v_val_1733_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_val_1733_);
lean_dec_ref_known(v_a_1732_, 1);
v___x_1734_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1733_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1734_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_val_1735_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_a_1732_, 1);
v___x_1736_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1737_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1736_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref_known(v___x_1737_, 1);
v___x_1738_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1735_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1738_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1739_; 
lean_dec(v_val_1735_);
lean_dec(v_declName_1301_);
v_a_1739_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1737_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1739_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v___x_1740_; 
lean_dec(v_a_1732_);
lean_inc(v_mvarId_1302_);
v___x_1740_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1302_, v___x_1572_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
if (lean_obj_tag(v_a_1741_) == 1)
{
lean_dec(v_a_1720_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1742_; lean_object* v___x_1743_; 
v_val_1742_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_val_1742_);
lean_dec_ref_known(v_a_1741_, 1);
v___x_1743_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1742_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1743_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v_val_1744_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_val_1744_);
lean_dec_ref_known(v_a_1741_, 1);
v___x_1745_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1746_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1745_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v___x_1747_; 
lean_dec_ref_known(v___x_1746_, 1);
v___x_1747_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1744_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1747_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1748_; 
lean_dec(v_val_1744_);
lean_dec(v_declName_1301_);
v_a_1748_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___x_1746_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1748_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; uint8_t v___x_1760_; uint8_t v___x_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_a_1741_);
v___x_1749_ = lean_unsigned_to_nat(100000u);
v___x_1750_ = lean_unsigned_to_nat(2u);
v___x_1751_ = 0;
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1753_, 0, v___x_1749_);
lean_ctor_set(v___x_1753_, 1, v___x_1750_);
lean_ctor_set(v___x_1753_, 2, v___x_1752_);
v___x_1754_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3, v___x_1754_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 1, v___x_1572_);
v___x_1755_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 2, v___x_1755_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 3, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 4, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 5, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 6, v___x_1751_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 7, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 8, v___x_1572_);
v___x_1756_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 9, v___x_1756_);
v___x_1757_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 10, v___x_1757_);
v___x_1758_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 11, v___x_1758_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 12, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 13, v___x_1572_);
v___x_1759_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 14, v___x_1759_);
v___x_1760_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 15, v___x_1760_);
v___x_1761_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 16, v___x_1761_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 17, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 18, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 19, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 20, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 21, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 22, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 23, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 24, v___x_1572_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 25, v___x_1572_);
v___x_1762_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 26, v___x_1762_);
v___x_1763_ = lean_unbox(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 27, v___x_1763_);
v___x_1764_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 28, v___x_1764_);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1767_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1768_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1769_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*2, v___x_1572_);
v___x_1770_ = l_Lean_Options_empty;
v___x_1771_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1753_, v___x_1766_, v___x_1769_, v___x_1770_, v_a_1303_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1302_);
v___x_1774_ = l_Lean_Meta_simpTargetStar(v_mvarId_1302_, v_a_1772_, v___x_1766_, v___x_1752_, v___x_1773_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v_fst_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1834_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v_fst_1776_ = lean_ctor_get(v_a_1775_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v_a_1775_, 1);
lean_dec(v_unused_1835_);
v___x_1778_ = v_a_1775_;
v_isShared_1779_ = v_isSharedCheck_1834_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_fst_1776_);
lean_dec(v_a_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1834_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
switch(lean_obj_tag(v_fst_1776_))
{
case 0:
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_box(0);
v___y_1527_ = v_a_1570_;
v___y_1528_ = v___x_1715_;
v_a_1529_ = v___x_1780_;
goto v___jp_1526_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1782_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1781_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1782_;
goto v___jp_1531_;
}
}
case 1:
{
lean_object* v___x_1783_; 
lean_inc(v_declName_1301_);
lean_inc(v_mvarId_1302_);
v___x_1783_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1302_, v_declName_1301_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
if (lean_obj_tag(v_a_1784_) == 1)
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1785_; lean_object* v___x_1786_; 
v_val_1785_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v_a_1784_, 1);
v___x_1786_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1785_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1786_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_val_1787_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v_a_1784_, 1);
v___x_1788_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1789_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1788_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v___x_1790_; 
lean_dec_ref_known(v___x_1789_, 1);
v___x_1790_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_val_1787_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1790_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1791_; 
lean_dec(v_val_1787_);
lean_dec(v_declName_1301_);
v_a_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1789_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1791_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v_a_1784_);
lean_inc(v_mvarId_1302_);
v___x_1792_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref_known(v___x_1792_, 1);
if (lean_obj_tag(v_a_1793_) == 1)
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_val_1794_ = lean_ctor_get(v_a_1793_, 0);
lean_inc(v_val_1794_);
lean_dec_ref_known(v_a_1793_, 1);
v___x_1795_ = lean_box(0);
v___x_1796_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1794_, v___x_1765_, v_declName_1301_, v___x_1795_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_val_1794_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1796_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_val_1797_ = lean_ctor_get(v_a_1793_, 0);
lean_inc(v_val_1797_);
lean_dec_ref_known(v_a_1793_, 1);
v___x_1798_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1799_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1798_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1797_, v___x_1765_, v_declName_1301_, v_a_1800_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_val_1797_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1801_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1802_; 
lean_dec(v_val_1797_);
lean_dec(v_declName_1301_);
v_a_1802_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1799_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1802_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v___x_1803_; 
lean_dec(v_a_1793_);
lean_inc(v_mvarId_1302_);
v___x_1803_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1302_, v___x_1572_, v___x_1572_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1823_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1823_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1823_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
if (lean_obj_tag(v_a_1804_) == 1)
{
lean_del_object(v___x_1806_);
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_val_1808_; lean_object* v___x_1809_; 
v_val_1808_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v_a_1804_, 1);
v___x_1809_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1301_, v_val_1808_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1809_;
goto v___jp_1531_;
}
else
{
lean_object* v_val_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_val_1810_ = lean_ctor_get(v_a_1804_, 0);
lean_inc(v_val_1810_);
lean_dec_ref_known(v_a_1804_, 1);
v___x_1811_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1812_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1811_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; 
lean_dec_ref_known(v___x_1812_, 1);
v___x_1813_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1301_, v_val_1810_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1813_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1814_; 
lean_dec(v_val_1810_);
lean_dec(v_declName_1301_);
v_a_1814_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1812_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1814_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
lean_dec(v_a_1804_);
lean_dec(v_declName_1301_);
v___x_1815_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1807_ == 0)
{
lean_ctor_set_tag(v___x_1806_, 1);
lean_ctor_set(v___x_1806_, 0, v_mvarId_1302_);
v___x_1817_ = v___x_1806_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_mvarId_1302_);
v___x_1817_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 7);
lean_ctor_set(v___x_1778_, 1, v___x_1817_);
lean_ctor_set(v___x_1778_, 0, v___x_1815_);
v___x_1819_ = v___x_1778_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1819_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1820_;
goto v___jp_1531_;
}
}
}
}
}
else
{
lean_object* v_a_1824_; 
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1824_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1803_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1824_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_1825_; 
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1825_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1792_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1825_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_1826_; 
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1826_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1783_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1826_;
goto v___jp_1521_;
}
}
default: 
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1302_);
if (v___x_1508_ == 0)
{
lean_object* v_mvarId_1827_; lean_object* v___x_1828_; 
v_mvarId_1827_ = lean_ctor_get(v_fst_1776_, 0);
lean_inc(v_mvarId_1827_);
lean_dec_ref_known(v_fst_1776_, 1);
v___x_1828_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_mvarId_1827_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1828_;
goto v___jp_1531_;
}
else
{
lean_object* v_mvarId_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_mvarId_1829_ = lean_ctor_get(v_fst_1776_, 0);
lean_inc(v_mvarId_1829_);
lean_dec_ref_known(v_fst_1776_, 1);
v___x_1830_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1831_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1830_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v___x_1832_; 
lean_dec_ref_known(v___x_1831_, 1);
v___x_1832_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1301_, v_mvarId_1829_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1832_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1833_; 
lean_dec(v_mvarId_1829_);
lean_dec(v_declName_1301_);
v_a_1833_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1831_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1833_;
goto v___jp_1521_;
}
}
}
}
}
}
else
{
lean_object* v_a_1836_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1836_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1774_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1836_;
goto v___jp_1521_;
}
}
else
{
lean_object* v_a_1837_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1837_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1771_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1837_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_1838_; 
lean_dec(v_a_1720_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1838_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1740_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1838_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_1839_; 
lean_dec(v_a_1720_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1839_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1731_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1839_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_1840_; 
lean_dec(v_a_1720_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1840_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1840_);
lean_dec_ref_known(v___x_1722_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1840_;
goto v___jp_1521_;
}
}
else
{
lean_dec(v_a_1720_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1841_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1842_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1844_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1843_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1845_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1846_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1844_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1847_;
goto v___jp_1521_;
}
}
}
}
else
{
lean_object* v_a_1848_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1848_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1719_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1848_;
goto v___jp_1521_;
}
}
else
{
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = lean_box(0);
v___x_1850_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1849_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1850_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1852_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1505_, v___x_1851_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1853_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
v___y_1532_ = v_a_1570_;
v___y_1533_ = v___x_1715_;
v___y_1534_ = v___x_1854_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1855_; 
v_a_1855_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1852_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1855_;
goto v___jp_1521_;
}
}
}
}
else
{
lean_object* v_a_1856_; 
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1856_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1716_, 1);
v___y_1522_ = v_a_1570_;
v___y_1523_ = v___x_1715_;
v_a_1524_ = v_a_1856_;
goto v___jp_1521_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v___f_1504_);
lean_dec(v_mvarId_1302_);
lean_dec(v_declName_1301_);
v_a_1857_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1569_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1569_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
v___jp_1308_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
return v___x_1310_;
}
v___jp_1311_:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1312_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2075_, lean_object* v_as_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
if (lean_obj_tag(v_as_2076_) == 0)
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
lean_dec(v_declName_2075_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
else
{
lean_object* v_head_2084_; lean_object* v_tail_2085_; lean_object* v___x_2086_; 
v_head_2084_ = lean_ctor_get(v_as_2076_, 0);
lean_inc(v_head_2084_);
v_tail_2085_ = lean_ctor_get(v_as_2076_, 1);
lean_inc(v_tail_2085_);
lean_dec_ref_known(v_as_2076_, 2);
lean_inc(v_declName_2075_);
v___x_2086_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2075_, v_head_2084_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_dec_ref_known(v___x_2086_, 1);
v_as_2076_ = v_tail_2085_;
goto _start;
}
else
{
lean_dec(v_tail_2085_);
lean_dec(v_declName_2075_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2088_, lean_object* v_as_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2088_, v_as_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2096_, lean_object* v___x_2097_, lean_object* v_declName_2098_, lean_object* v_____r_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2096_, v___x_2097_, v_declName_2098_, v_____r_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___x_2097_);
lean_dec_ref(v_val_2096_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2106_, lean_object* v_as_2107_, lean_object* v_i_2108_, lean_object* v_stop_2109_, lean_object* v_b_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
size_t v_i_boxed_2116_; size_t v_stop_boxed_2117_; lean_object* v_res_2118_; 
v_i_boxed_2116_ = lean_unbox_usize(v_i_2108_);
lean_dec(v_i_2108_);
v_stop_boxed_2117_ = lean_unbox_usize(v_stop_2109_);
lean_dec(v_stop_2109_);
v_res_2118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2106_, v_as_2107_, v_i_boxed_2116_, v_stop_boxed_2117_, v_b_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v_as_2107_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2119_, lean_object* v_mvarId_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2119_, v_mvarId_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_00_u03b1_2127_, lean_object* v_x_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_2128_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_x_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_00_u03b1_2135_, v_x_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2143_, uint8_t v_skipRealize_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; lean_object* v_env_2148_; uint8_t v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2147_ = lean_st_ref_get(v___y_2145_);
v_env_2148_ = lean_ctor_get(v___x_2147_, 0);
lean_inc_ref(v_env_2148_);
lean_dec(v___x_2147_);
v___x_2149_ = l_Lean_Environment_contains(v_env_2148_, v_constName_2143_, v_skipRealize_2144_);
v___x_2150_ = lean_box(v___x_2149_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2152_, lean_object* v_skipRealize_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
uint8_t v_skipRealize_boxed_2156_; lean_object* v_res_2157_; 
v_skipRealize_boxed_2156_ = lean_unbox(v_skipRealize_2153_);
v_res_2157_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2152_, v_skipRealize_boxed_2156_, v___y_2154_);
lean_dec(v___y_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2158_, uint8_t v_skipRealize_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2158_, v_skipRealize_2159_, v___y_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2166_, lean_object* v_skipRealize_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v_skipRealize_boxed_2173_; lean_object* v_res_2174_; 
v_skipRealize_boxed_2173_ = lean_unbox(v_skipRealize_2167_);
v_res_2174_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2166_, v_skipRealize_boxed_2173_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2175_, lean_object* v___x_2176_, lean_object* v___x_2177_, lean_object* v_snd_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
lean_inc_ref(v_snd_2175_);
v___x_2184_ = l_Lean_Meta_mkCongrArg(v_snd_2175_, v___x_2176_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref_known(v___x_2184_, 1);
v___x_2186_ = l_Lean_Expr_app___override(v_snd_2175_, v___x_2177_);
v___x_2187_ = l_Lean_MVarId_replaceTargetEq(v_snd_2178_, v___x_2186_, v_a_2185_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2187_;
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_snd_2178_);
lean_dec_ref(v___x_2177_);
lean_dec_ref(v_snd_2175_);
v_a_2188_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2184_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2184_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2196_, lean_object* v___x_2197_, lean_object* v___x_2198_, lean_object* v_snd_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2196_, v___x_2197_, v___x_2198_, v_snd_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2205_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2215_ = l_Lean_stringToMessageData(v___x_2214_);
return v___x_2215_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2224_ = l_Lean_stringToMessageData(v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2228_, lean_object* v___x_2229_, lean_object* v_cls_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
lean_inc(v_mvarId_2228_);
v___x_2236_ = l_Lean_MVarId_getType(v_mvarId_2228_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2236_, 1);
v___x_2238_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2237_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v_fst_2240_; lean_object* v_snd_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2395_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v_fst_2240_ = lean_ctor_get(v_a_2239_, 0);
v_snd_2241_ = lean_ctor_get(v_a_2239_, 1);
v_isSharedCheck_2395_ = !lean_is_exclusive(v_a_2239_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2243_ = v_a_2239_;
v_isShared_2244_ = v_isSharedCheck_2395_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_snd_2241_);
lean_inc(v_fst_2240_);
lean_dec(v_a_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2395_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v_dummy_2250_; lean_object* v_nargs_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; uint8_t v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2394_; 
v___x_2245_ = l_Lean_Expr_getAppFn(v_fst_2240_);
v___x_2246_ = l_Lean_Expr_constName_x21(v___x_2245_);
v___x_2247_ = l_Lean_Expr_constLevels_x21(v___x_2245_);
lean_dec_ref(v___x_2245_);
v___x_2248_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2249_ = l_Lean_Name_str___override(v___x_2246_, v___x_2248_);
v_dummy_2250_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_2251_ = l_Lean_Expr_getAppNumArgs(v_fst_2240_);
lean_inc(v_nargs_2251_);
v___x_2252_ = lean_mk_array(v_nargs_2251_, v_dummy_2250_);
v___x_2253_ = lean_unsigned_to_nat(1u);
v___x_2254_ = lean_nat_sub(v_nargs_2251_, v___x_2253_);
lean_dec(v_nargs_2251_);
v___x_2255_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2240_, v___x_2252_, v___x_2254_);
v___x_2369_ = 1;
lean_inc(v___x_2249_);
v___x_2370_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2249_, v___x_2369_, v___y_2234_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2394_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2394_;
goto v_resetjp_2372_;
}
v___jp_2256_:
{
lean_object* v___x_2265_; 
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc_ref(v___y_2257_);
v___x_2265_ = lean_infer_type(v___y_2257_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2268_ = l_Lean_MVarId_define(v_mvarId_2228_, v___x_2267_, v_a_2266_, v___y_2257_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___x_2270_ = l_Lean_Meta_intro1Core(v_a_2269_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v_fst_2272_; lean_object* v_snd_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v_fst_2272_ = lean_ctor_get(v_a_2271_, 0);
lean_inc(v_fst_2272_);
v_snd_2273_ = lean_ctor_get(v_a_2271_, 1);
lean_inc_n(v_snd_2273_, 2);
lean_dec(v_a_2271_);
v___x_2274_ = l_Lean_Expr_appFn_x21(v___y_2259_);
lean_dec_ref(v___y_2259_);
v___x_2275_ = l_Lean_mkFVar(v_fst_2272_);
v___x_2276_ = l_Lean_Expr_app___override(v___x_2274_, v___x_2275_);
v___x_2277_ = l_Lean_mkAppN(v___y_2258_, v___x_2255_);
lean_dec_ref(v___x_2255_);
v___f_2278_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2278_, 0, v_snd_2241_);
lean_closure_set(v___f_2278_, 1, v___x_2277_);
lean_closure_set(v___f_2278_, 2, v___x_2276_);
lean_closure_set(v___f_2278_, 3, v_snd_2273_);
v___x_2279_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2273_, v___f_2278_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v___x_2279_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2241_);
v_a_2280_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2270_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2270_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2241_);
return v___x_2268_;
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2241_);
lean_dec(v_mvarId_2228_);
v_a_2288_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2265_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2265_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
v___jp_2296_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
lean_inc(v___x_2249_);
v___x_2301_ = l_Lean_mkConst(v___x_2249_, v___x_2247_);
lean_inc(v___y_2300_);
lean_inc_ref(v___y_2299_);
lean_inc(v___y_2298_);
lean_inc_ref(v___y_2297_);
lean_inc_ref(v___x_2301_);
v___x_2302_ = lean_infer_type(v___x_2301_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Meta_instantiateForall(v_a_2303_, v___x_2255_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v___x_2306_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2307_ = lean_unsigned_to_nat(3u);
v___x_2308_ = l_Lean_Expr_isAppOfArity(v_a_2305_, v___x_2306_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
lean_dec(v_a_2305_);
lean_dec_ref(v___x_2301_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2241_);
lean_dec(v_cls_2230_);
v___x_2309_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2310_ = l_Lean_MessageData_ofName(v___x_2249_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 7);
lean_ctor_set(v___x_2243_, 1, v___x_2310_);
lean_ctor_set(v___x_2243_, 0, v___x_2309_);
v___x_2312_ = v___x_2243_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2313_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2315_, 0, v_mvarId_2228_);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
v___x_2317_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2316_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
return v___x_2317_;
}
}
else
{
lean_object* v_toCold_2319_; lean_object* v_options_2320_; lean_object* v_inheritedTraceOptions_2321_; uint8_t v_hasTrace_2322_; lean_object* v___x_2323_; lean_object* v_nargs_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_dec(v___x_2249_);
v_toCold_2319_ = lean_ctor_get(v___y_2299_, 0);
v_options_2320_ = lean_ctor_get(v_toCold_2319_, 2);
v_inheritedTraceOptions_2321_ = lean_ctor_get(v_toCold_2319_, 11);
v_hasTrace_2322_ = lean_ctor_get_uint8(v_options_2320_, sizeof(void*)*1);
v___x_2323_ = l_Lean_Expr_appArg_x21(v_a_2305_);
lean_dec(v_a_2305_);
v_nargs_2324_ = l_Lean_Expr_getAppNumArgs(v___x_2323_);
lean_inc(v_nargs_2324_);
v___x_2325_ = lean_mk_array(v_nargs_2324_, v_dummy_2250_);
v___x_2326_ = lean_nat_sub(v_nargs_2324_, v___x_2253_);
lean_dec(v_nargs_2324_);
lean_inc_ref(v___x_2323_);
v___x_2327_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2323_, v___x_2325_, v___x_2326_);
v___x_2328_ = lean_array_get_size(v___x_2327_);
v___x_2329_ = lean_nat_sub(v___x_2328_, v___x_2253_);
v___x_2330_ = lean_array_get(v___x_2229_, v___x_2327_, v___x_2329_);
lean_dec(v___x_2329_);
lean_dec_ref(v___x_2327_);
if (v_hasTrace_2322_ == 0)
{
lean_del_object(v___x_2243_);
lean_dec(v_cls_2230_);
v___y_2257_ = v___x_2330_;
v___y_2258_ = v___x_2301_;
v___y_2259_ = v___x_2323_;
v___y_2260_ = v___x_2308_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v___x_2331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2230_);
v___x_2332_ = l_Lean_Name_append(v___x_2331_, v_cls_2230_);
v___x_2333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2321_, v_options_2320_, v___x_2332_);
lean_dec(v___x_2332_);
if (v___x_2333_ == 0)
{
lean_del_object(v___x_2243_);
lean_dec(v_cls_2230_);
v___y_2257_ = v___x_2330_;
v___y_2258_ = v___x_2301_;
v___y_2259_ = v___x_2323_;
v___y_2260_ = v___x_2308_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2334_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2335_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2330_);
v___x_2336_ = l_Lean_inlineExpr(v___x_2330_, v___x_2335_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 7);
lean_ctor_set(v___x_2243_, 1, v___x_2336_);
lean_ctor_set(v___x_2243_, 0, v___x_2334_);
v___x_2338_ = v___x_2243_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2339_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
lean_inc_ref(v___x_2323_);
v___x_2341_ = l_Lean_indentExpr(v___x_2323_);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2230_, v___x_2342_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_dec_ref_known(v___x_2343_, 1);
v___y_2257_ = v___x_2330_;
v___y_2258_ = v___x_2301_;
v___y_2259_ = v___x_2323_;
v___y_2260_ = v___x_2308_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v___x_2330_);
lean_dec_ref(v___x_2323_);
lean_dec_ref(v___x_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2241_);
lean_dec(v_mvarId_2228_);
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
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
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v___x_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v___x_2255_);
lean_dec(v___x_2249_);
lean_del_object(v___x_2243_);
lean_dec(v_snd_2241_);
lean_dec(v_cls_2230_);
lean_dec(v_mvarId_2228_);
v_a_2353_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2304_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2304_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v___x_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v___x_2255_);
lean_dec(v___x_2249_);
lean_del_object(v___x_2243_);
lean_dec(v_snd_2241_);
lean_dec(v_cls_2230_);
lean_dec(v_mvarId_2228_);
v_a_2361_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2302_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2302_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
v_resetjp_2372_:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_unbox(v_a_2371_);
lean_dec(v_a_2371_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
lean_dec_ref(v___x_2255_);
lean_dec(v___x_2247_);
lean_del_object(v___x_2243_);
lean_dec(v_snd_2241_);
lean_dec(v_cls_2230_);
v___x_2376_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2377_ = l_Lean_MessageData_ofName(v___x_2249_);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2378_);
lean_ctor_set(v___x_2380_, 1, v___x_2379_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set_tag(v___x_2373_, 1);
lean_ctor_set(v___x_2373_, 0, v_mvarId_2228_);
v___x_2382_ = v___x_2373_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_mvarId_2228_);
v___x_2382_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
v___x_2383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2380_);
lean_ctor_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2383_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2384_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2384_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_del_object(v___x_2373_);
v___y_2297_ = v___y_2231_;
v___y_2298_ = v___y_2232_;
v___y_2299_ = v___y_2233_;
v___y_2300_ = v___y_2234_;
goto v___jp_2296_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v_cls_2230_);
lean_dec(v_mvarId_2228_);
v_a_2396_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2238_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2238_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v_cls_2230_);
lean_dec(v_mvarId_2228_);
v_a_2404_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2236_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2236_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2412_, lean_object* v___x_2413_, lean_object* v_cls_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2412_, v___x_2413_, v_cls_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec_ref(v___x_2413_);
return v_res_2420_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2431_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2432_, 0, v_mvarId_2424_);
v___x_2433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2435_, v_x_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec_ref(v_x_2436_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2443_, lean_object* v_mvarId_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v_toCold_2450_; lean_object* v_options_2451_; lean_object* v_inheritedTraceOptions_2452_; uint8_t v_hasTrace_2453_; lean_object* v___x_2454_; lean_object* v_cls_2455_; lean_object* v___f_2456_; 
v_toCold_2450_ = lean_ctor_get(v_a_2447_, 0);
v_options_2451_ = lean_ctor_get(v_toCold_2450_, 2);
v_inheritedTraceOptions_2452_ = lean_ctor_get(v_toCold_2450_, 11);
v_hasTrace_2453_ = lean_ctor_get_uint8(v_options_2451_, sizeof(void*)*1);
v___x_2454_ = l_Lean_instInhabitedExpr;
v_cls_2455_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2444_);
v___f_2456_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2456_, 0, v_mvarId_2444_);
lean_closure_set(v___f_2456_, 1, v___x_2454_);
lean_closure_set(v___f_2456_, 2, v_cls_2455_);
if (v_hasTrace_2453_ == 0)
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2444_, v___f_2456_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref_known(v___x_2457_, 1);
v___x_2459_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2443_, v_a_2458_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2459_;
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_declName_2443_);
v_a_2460_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2457_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2457_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v_a_2475_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v_a_2490_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v_a_2495_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v_a_2507_; 
lean_inc(v_mvarId_2444_);
v___f_2468_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2468_, 0, v_mvarId_2444_);
v___x_2469_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2470_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2471_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2452_, v_options_2451_, v___x_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = l_Lean_trace_profiler;
v___x_2543_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2451_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
lean_dec_ref(v___f_2468_);
v___x_2544_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2444_, v___f_2456_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2443_, v_a_2545_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2546_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_declName_2443_);
v_a_2547_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2544_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2544_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
else
{
goto v___jp_2509_;
}
}
else
{
goto v___jp_2509_;
}
v___jp_2472_:
{
lean_object* v___x_2476_; double v___x_2477_; double v___x_2478_; double v___x_2479_; double v___x_2480_; double v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2476_ = lean_io_mono_nanos_now();
v___x_2477_ = lean_float_of_nat(v___y_2474_);
v___x_2478_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2479_ = lean_float_div(v___x_2477_, v___x_2478_);
v___x_2480_ = lean_float_of_nat(v___x_2476_);
v___x_2481_ = lean_float_div(v___x_2480_, v___x_2478_);
v___x_2482_ = lean_box_float(v___x_2479_);
v___x_2483_ = lean_box_float(v___x_2481_);
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2482_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_a_2475_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2455_, v_hasTrace_2453_, v___x_2469_, v_options_2451_, v___x_2471_, v___y_2473_, v___f_2468_, v___x_2485_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2486_;
}
v___jp_2487_:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v_a_2490_);
v___y_2473_ = v___y_2488_;
v___y_2474_ = v___y_2489_;
v_a_2475_ = v___x_2491_;
goto v___jp_2472_;
}
v___jp_2492_:
{
lean_object* v___x_2496_; double v___x_2497_; double v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2496_ = lean_io_get_num_heartbeats();
v___x_2497_ = lean_float_of_nat(v___y_2493_);
v___x_2498_ = lean_float_of_nat(v___x_2496_);
v___x_2499_ = lean_box_float(v___x_2497_);
v___x_2500_ = lean_box_float(v___x_2498_);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v_a_2495_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2455_, v_hasTrace_2453_, v___x_2469_, v_options_2451_, v___x_2471_, v___y_2494_, v___f_2468_, v___x_2502_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v___x_2503_;
}
v___jp_2504_:
{
lean_object* v___x_2508_; 
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v_a_2507_);
v___y_2493_ = v___y_2505_;
v___y_2494_ = v___y_2506_;
v_a_2495_ = v___x_2508_;
goto v___jp_2492_;
}
v___jp_2509_:
{
lean_object* v___x_2510_; lean_object* v_a_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2510_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2448_);
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2513_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2451_, v___x_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_io_mono_nanos_now();
v___x_2515_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2444_, v___f_2456_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2443_, v_a_2516_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
lean_ctor_set_tag(v___x_2520_, 1);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
v___y_2473_ = v_a_2511_;
v___y_2474_ = v___x_2514_;
v_a_2475_ = v___x_2523_;
goto v___jp_2472_;
}
}
}
else
{
lean_object* v_a_2526_; 
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2517_, 1);
v___y_2488_ = v_a_2511_;
v___y_2489_ = v___x_2514_;
v_a_2490_ = v_a_2526_;
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_2527_; 
lean_dec(v_declName_2443_);
v_a_2527_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2515_, 1);
v___y_2488_ = v_a_2511_;
v___y_2489_ = v___x_2514_;
v_a_2490_ = v_a_2527_;
goto v___jp_2487_;
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = lean_io_get_num_heartbeats();
v___x_2529_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2444_, v___f_2456_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2443_, v_a_2530_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set_tag(v___x_2534_, 1);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
v___y_2493_ = v___x_2528_;
v___y_2494_ = v_a_2511_;
v_a_2495_ = v___x_2537_;
goto v___jp_2492_;
}
}
}
else
{
lean_object* v_a_2540_; 
v_a_2540_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2531_, 1);
v___y_2505_ = v___x_2528_;
v___y_2506_ = v_a_2511_;
v_a_2507_ = v_a_2540_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2541_; 
lean_dec(v_declName_2443_);
v_a_2541_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2529_, 1);
v___y_2505_ = v___x_2528_;
v___y_2506_ = v_a_2511_;
v_a_2507_ = v_a_2541_;
goto v___jp_2504_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2555_, lean_object* v_mvarId_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2555_, v_mvarId_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2563_, lean_object* v___y_2564_){
_start:
{
uint8_t v___x_2566_; 
v___x_2566_ = l_Lean_Expr_hasMVar(v_e_2563_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_e_2563_);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; lean_object* v_mctx_2569_; lean_object* v___x_2570_; lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2573_; lean_object* v_cache_2574_; lean_object* v_zetaDeltaFVarIds_2575_; lean_object* v_postponed_2576_; lean_object* v_diag_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2586_; 
v___x_2568_ = lean_st_ref_get(v___y_2564_);
v_mctx_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc_ref(v_mctx_2569_);
lean_dec(v___x_2568_);
v___x_2570_ = l_Lean_instantiateMVarsCore(v_mctx_2569_, v_e_2563_);
v_fst_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_fst_2571_);
v_snd_2572_ = lean_ctor_get(v___x_2570_, 1);
lean_inc(v_snd_2572_);
lean_dec_ref(v___x_2570_);
v___x_2573_ = lean_st_ref_take(v___y_2564_);
v_cache_2574_ = lean_ctor_get(v___x_2573_, 1);
v_zetaDeltaFVarIds_2575_ = lean_ctor_get(v___x_2573_, 2);
v_postponed_2576_ = lean_ctor_get(v___x_2573_, 3);
v_diag_2577_ = lean_ctor_get(v___x_2573_, 4);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v___x_2573_, 0);
lean_dec(v_unused_2587_);
v___x_2579_ = v___x_2573_;
v_isShared_2580_ = v_isSharedCheck_2586_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_diag_2577_);
lean_inc(v_postponed_2576_);
lean_inc(v_zetaDeltaFVarIds_2575_);
lean_inc(v_cache_2574_);
lean_dec(v___x_2573_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2586_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 0, v_snd_2572_);
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_snd_2572_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v_cache_2574_);
lean_ctor_set(v_reuseFailAlloc_2585_, 2, v_zetaDeltaFVarIds_2575_);
lean_ctor_set(v_reuseFailAlloc_2585_, 3, v_postponed_2576_);
lean_ctor_set(v_reuseFailAlloc_2585_, 4, v_diag_2577_);
v___x_2582_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = lean_st_ref_put(v___y_2564_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_fst_2571_);
return v___x_2584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2588_, v___y_2589_);
lean_dec(v___y_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2592_, v___y_2594_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2606_, uint8_t v_allowLevelAssignments_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2607_, v_k_2606_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
v_a_2622_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2613_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2613_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2630_, lean_object* v_allowLevelAssignments_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2637_; lean_object* v_res_2638_; 
v_allowLevelAssignments_boxed_2637_ = lean_unbox(v_allowLevelAssignments_2631_);
v_res_2638_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2630_, v_allowLevelAssignments_boxed_2637_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2639_, lean_object* v_k_2640_, uint8_t v_allowLevelAssignments_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2640_, v_allowLevelAssignments_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2648_, lean_object* v_k_2649_, lean_object* v_allowLevelAssignments_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2656_; lean_object* v_res_2657_; 
v_allowLevelAssignments_boxed_2656_ = lean_unbox(v_allowLevelAssignments_2650_);
v_res_2657_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2648_, v_k_2649_, v_allowLevelAssignments_boxed_2656_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2658_, lean_object* v_e_2659_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = l_Lean_indentD(v_e_2659_);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2658_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
return v___x_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2662_, lean_object* v___x_2663_, lean_object* v_declName_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2662_, v___x_2663_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = l_Lean_Expr_mvarId_x21(v_a_2671_);
v___x_2673_ = l_Lean_MVarId_intros(v___x_2672_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v_snd_2675_; lean_object* v___x_2676_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v_snd_2675_ = lean_ctor_get(v_a_2674_, 1);
lean_inc_n(v_snd_2675_, 2);
lean_dec(v_a_2674_);
v___x_2676_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2675_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; uint8_t v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = lean_unbox(v_a_2677_);
lean_dec(v_a_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2675_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2681_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2664_, v_a_2680_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v___x_2682_; 
lean_dec_ref_known(v___x_2681_, 1);
v___x_2682_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2671_, v___y_2666_);
return v___x_2682_;
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_a_2671_);
v_a_2683_ = lean_ctor_get(v___x_2681_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2681_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2681_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2681_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_a_2671_);
lean_dec(v_declName_2664_);
v_a_2691_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2679_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2679_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
else
{
lean_object* v___x_2699_; 
lean_dec(v_snd_2675_);
lean_dec(v_declName_2664_);
v___x_2699_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2671_, v___y_2666_);
return v___x_2699_;
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_snd_2675_);
lean_dec(v_a_2671_);
lean_dec(v_declName_2664_);
v_a_2700_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2676_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2676_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
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
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec(v_a_2671_);
lean_dec(v_declName_2664_);
v_a_2708_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2673_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2673_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_dec(v_declName_2664_);
return v___x_2670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2716_, lean_object* v___x_2717_, lean_object* v_declName_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2716_, v___x_2717_, v_declName_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
return v_res_2724_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2727_ = l_Lean_stringToMessageData(v___x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2728_, lean_object* v_x_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2735_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2736_ = l_Lean_indentExpr(v_type_2728_);
v___x_2737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
lean_ctor_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2739_, v_x_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec_ref(v_x_2740_);
return v_res_2746_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2747_){
_start:
{
if (lean_obj_tag(v_e_2747_) == 0)
{
uint8_t v___x_2748_; 
v___x_2748_ = 2;
return v___x_2748_;
}
else
{
lean_object* v_a_2749_; uint8_t v___x_2750_; 
v_a_2749_ = lean_ctor_get(v_e_2747_, 0);
v___x_2750_ = l_Lean_Expr_hasSyntheticSorry(v_a_2749_);
if (v___x_2750_ == 0)
{
uint8_t v___x_2751_; 
v___x_2751_ = 0;
return v___x_2751_;
}
else
{
uint8_t v___x_2752_; 
v___x_2752_ = 1;
return v___x_2752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2753_){
_start:
{
uint8_t v_res_2754_; lean_object* v_r_2755_; 
v_res_2754_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2753_);
lean_dec_ref(v_e_2753_);
v_r_2755_ = lean_box(v_res_2754_);
return v_r_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2756_, uint8_t v_collapsed_2757_, lean_object* v_tag_2758_, lean_object* v_opts_2759_, uint8_t v_clsEnabled_2760_, lean_object* v_oldTraces_2761_, lean_object* v_msg_2762_, lean_object* v_resStartStop_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_fst_2769_; lean_object* v_snd_2770_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v_data_2774_; lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; lean_object* v___y_2790_; lean_object* v_a_2791_; uint8_t v___y_2806_; double v___y_2838_; 
v_fst_2769_ = lean_ctor_get(v_resStartStop_2763_, 0);
lean_inc(v_fst_2769_);
v_snd_2770_ = lean_ctor_get(v_resStartStop_2763_, 1);
lean_inc(v_snd_2770_);
lean_dec_ref(v_resStartStop_2763_);
v_fst_2785_ = lean_ctor_get(v_snd_2770_, 0);
lean_inc(v_fst_2785_);
v_snd_2786_ = lean_ctor_get(v_snd_2770_, 1);
lean_inc(v_snd_2786_);
lean_dec(v_snd_2770_);
v___x_2787_ = l_Lean_trace_profiler;
v___x_2788_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2759_, v___x_2787_);
if (v___x_2788_ == 0)
{
v___y_2806_ = v___x_2788_;
goto v___jp_2805_;
}
else
{
lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2844_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2759_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; double v___x_2847_; double v___x_2848_; double v___x_2849_; 
v___x_2845_ = l_Lean_trace_profiler_threshold;
v___x_2846_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2759_, v___x_2845_);
v___x_2847_ = lean_float_of_nat(v___x_2846_);
v___x_2848_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_2849_ = lean_float_div(v___x_2847_, v___x_2848_);
v___y_2838_ = v___x_2849_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; double v___x_2852_; 
v___x_2850_ = l_Lean_trace_profiler_threshold;
v___x_2851_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2759_, v___x_2850_);
v___x_2852_ = lean_float_of_nat(v___x_2851_);
v___y_2838_ = v___x_2852_;
goto v___jp_2837_;
}
}
v___jp_2771_:
{
lean_object* v___x_2775_; 
lean_inc(v___y_2772_);
v___x_2775_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_2761_, v_data_2774_, v___y_2772_, v___y_2773_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v___x_2776_; 
lean_dec_ref_known(v___x_2775_, 1);
v___x_2776_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2769_);
return v___x_2776_;
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec(v_fst_2769_);
v_a_2777_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2775_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2775_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
v___jp_2789_:
{
uint8_t v_result_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; double v___x_2795_; lean_object* v_data_2796_; 
v_result_2792_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2769_);
v___x_2793_ = lean_box(v_result_2792_);
v___x_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
v___x_2795_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2758_);
lean_inc_ref(v___x_2794_);
lean_inc(v_cls_2756_);
v_data_2796_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2796_, 0, v_cls_2756_);
lean_ctor_set(v_data_2796_, 1, v___x_2794_);
lean_ctor_set(v_data_2796_, 2, v_tag_2758_);
lean_ctor_set_float(v_data_2796_, sizeof(void*)*3, v___x_2795_);
lean_ctor_set_float(v_data_2796_, sizeof(void*)*3 + 8, v___x_2795_);
lean_ctor_set_uint8(v_data_2796_, sizeof(void*)*3 + 16, v_collapsed_2757_);
if (v___x_2788_ == 0)
{
lean_dec_ref_known(v___x_2794_, 1);
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_dec_ref(v_tag_2758_);
lean_dec(v_cls_2756_);
v___y_2772_ = v___y_2790_;
v___y_2773_ = v_a_2791_;
v_data_2774_ = v_data_2796_;
goto v___jp_2771_;
}
else
{
lean_object* v_data_2797_; double v___x_2798_; double v___x_2799_; 
lean_dec_ref_known(v_data_2796_, 3);
v_data_2797_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2797_, 0, v_cls_2756_);
lean_ctor_set(v_data_2797_, 1, v___x_2794_);
lean_ctor_set(v_data_2797_, 2, v_tag_2758_);
v___x_2798_ = lean_unbox_float(v_fst_2785_);
lean_dec(v_fst_2785_);
lean_ctor_set_float(v_data_2797_, sizeof(void*)*3, v___x_2798_);
v___x_2799_ = lean_unbox_float(v_snd_2786_);
lean_dec(v_snd_2786_);
lean_ctor_set_float(v_data_2797_, sizeof(void*)*3 + 8, v___x_2799_);
lean_ctor_set_uint8(v_data_2797_, sizeof(void*)*3 + 16, v_collapsed_2757_);
v___y_2772_ = v___y_2790_;
v___y_2773_ = v_a_2791_;
v_data_2774_ = v_data_2797_;
goto v___jp_2771_;
}
}
v___jp_2800_:
{
lean_object* v_ref_2801_; lean_object* v___x_2802_; 
v_ref_2801_ = lean_ctor_get(v___y_2766_, 2);
lean_inc(v___y_2767_);
lean_inc_ref(v___y_2766_);
lean_inc(v___y_2765_);
lean_inc_ref(v___y_2764_);
lean_inc(v_fst_2769_);
v___x_2802_ = lean_apply_6(v_msg_2762_, v_fst_2769_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, lean_box(0));
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___y_2790_ = v_ref_2801_;
v_a_2791_ = v_a_2803_;
goto v___jp_2789_;
}
else
{
lean_object* v___x_2804_; 
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_2790_ = v_ref_2801_;
v_a_2791_ = v___x_2804_;
goto v___jp_2789_;
}
}
v___jp_2805_:
{
if (v_clsEnabled_2760_ == 0)
{
if (v___y_2806_ == 0)
{
lean_object* v___x_2807_; lean_object* v_traceState_2808_; lean_object* v_env_2809_; lean_object* v_nextMacroScope_2810_; lean_object* v_ngen_2811_; lean_object* v_auxDeclNGen_2812_; lean_object* v_cache_2813_; lean_object* v_recordedDeps_2814_; lean_object* v_messages_2815_; lean_object* v_infoState_2816_; lean_object* v_snapshotTasks_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_snd_2786_);
lean_dec(v_fst_2785_);
lean_dec_ref(v_msg_2762_);
lean_dec_ref(v_tag_2758_);
lean_dec(v_cls_2756_);
v___x_2807_ = lean_st_ref_take(v___y_2767_);
v_traceState_2808_ = lean_ctor_get(v___x_2807_, 4);
v_env_2809_ = lean_ctor_get(v___x_2807_, 0);
v_nextMacroScope_2810_ = lean_ctor_get(v___x_2807_, 1);
v_ngen_2811_ = lean_ctor_get(v___x_2807_, 2);
v_auxDeclNGen_2812_ = lean_ctor_get(v___x_2807_, 3);
v_cache_2813_ = lean_ctor_get(v___x_2807_, 5);
v_recordedDeps_2814_ = lean_ctor_get(v___x_2807_, 6);
v_messages_2815_ = lean_ctor_get(v___x_2807_, 7);
v_infoState_2816_ = lean_ctor_get(v___x_2807_, 8);
v_snapshotTasks_2817_ = lean_ctor_get(v___x_2807_, 9);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2819_ = v___x_2807_;
v_isShared_2820_ = v_isSharedCheck_2836_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_snapshotTasks_2817_);
lean_inc(v_infoState_2816_);
lean_inc(v_messages_2815_);
lean_inc(v_recordedDeps_2814_);
lean_inc(v_cache_2813_);
lean_inc(v_traceState_2808_);
lean_inc(v_auxDeclNGen_2812_);
lean_inc(v_ngen_2811_);
lean_inc(v_nextMacroScope_2810_);
lean_inc(v_env_2809_);
lean_dec(v___x_2807_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2836_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
uint64_t v_tid_2821_; lean_object* v_traces_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2835_; 
v_tid_2821_ = lean_ctor_get_uint64(v_traceState_2808_, sizeof(void*)*1);
v_traces_2822_ = lean_ctor_get(v_traceState_2808_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_traceState_2808_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2824_ = v_traceState_2808_;
v_isShared_2825_ = v_isSharedCheck_2835_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_traces_2822_);
lean_dec(v_traceState_2808_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2835_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2828_; 
v___x_2826_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2761_, v_traces_2822_);
lean_dec_ref(v_traces_2822_);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2826_);
v___x_2828_ = v___x_2824_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2826_);
lean_ctor_set_uint64(v_reuseFailAlloc_2834_, sizeof(void*)*1, v_tid_2821_);
v___x_2828_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2830_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 4, v___x_2828_);
v___x_2830_ = v___x_2819_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_env_2809_);
lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_nextMacroScope_2810_);
lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_ngen_2811_);
lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_auxDeclNGen_2812_);
lean_ctor_set(v_reuseFailAlloc_2833_, 4, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2833_, 5, v_cache_2813_);
lean_ctor_set(v_reuseFailAlloc_2833_, 6, v_recordedDeps_2814_);
lean_ctor_set(v_reuseFailAlloc_2833_, 7, v_messages_2815_);
lean_ctor_set(v_reuseFailAlloc_2833_, 8, v_infoState_2816_);
lean_ctor_set(v_reuseFailAlloc_2833_, 9, v_snapshotTasks_2817_);
v___x_2830_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_st_ref_put(v___y_2767_, v___x_2830_);
v___x_2832_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2769_);
return v___x_2832_;
}
}
}
}
}
else
{
goto v___jp_2800_;
}
}
else
{
goto v___jp_2800_;
}
}
v___jp_2837_:
{
double v___x_2839_; double v___x_2840_; double v___x_2841_; uint8_t v___x_2842_; 
v___x_2839_ = lean_unbox_float(v_snd_2786_);
v___x_2840_ = lean_unbox_float(v_fst_2785_);
v___x_2841_ = lean_float_sub(v___x_2839_, v___x_2840_);
v___x_2842_ = lean_float_decLt(v___y_2838_, v___x_2841_);
v___y_2806_ = v___x_2842_;
goto v___jp_2805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2853_, lean_object* v_collapsed_2854_, lean_object* v_tag_2855_, lean_object* v_opts_2856_, lean_object* v_clsEnabled_2857_, lean_object* v_oldTraces_2858_, lean_object* v_msg_2859_, lean_object* v_resStartStop_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
uint8_t v_collapsed_boxed_2866_; uint8_t v_clsEnabled_boxed_2867_; lean_object* v_res_2868_; 
v_collapsed_boxed_2866_ = lean_unbox(v_collapsed_2854_);
v_clsEnabled_boxed_2867_ = lean_unbox(v_clsEnabled_2857_);
v_res_2868_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2853_, v_collapsed_boxed_2866_, v_tag_2855_, v_opts_2856_, v_clsEnabled_boxed_2867_, v_oldTraces_2858_, v_msg_2859_, v_resStartStop_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v_opts_2856_);
return v_res_2868_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2871_ = l_Lean_stringToMessageData(v___x_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2874_ = l_Lean_stringToMessageData(v___x_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2875_, lean_object* v_type_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_toCold_2882_; lean_object* v_options_2883_; lean_object* v_inheritedTraceOptions_2884_; uint8_t v_hasTrace_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___f_2892_; lean_object* v___x_2893_; lean_object* v___f_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_toCold_2882_ = lean_ctor_get(v_a_2879_, 0);
v_options_2883_ = lean_ctor_get(v_toCold_2882_, 2);
v_inheritedTraceOptions_2884_ = lean_ctor_get(v_toCold_2882_, 11);
v_hasTrace_2885_ = lean_ctor_get_uint8(v_options_2883_, sizeof(void*)*1);
v___x_2886_ = 0;
lean_inc(v_declName_2875_);
v___x_2887_ = l_Lean_MessageData_ofConstName(v_declName_2875_, v___x_2886_);
v___x_2888_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v___x_2887_);
v___x_2890_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_2891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
v___f_2892_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_2892_, 0, v___x_2891_);
v___x_2893_ = lean_box(0);
lean_inc_ref(v_type_2876_);
v___f_2894_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2894_, 0, v_type_2876_);
lean_closure_set(v___f_2894_, 1, v___x_2893_);
lean_closure_set(v___f_2894_, 2, v_declName_2875_);
v___x_2895_ = lean_box(v___x_2886_);
v___x_2896_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2896_, 0, lean_box(0));
lean_closure_set(v___x_2896_, 1, v___f_2894_);
lean_closure_set(v___x_2896_, 2, v___x_2895_);
if (v_hasTrace_2885_ == 0)
{
lean_object* v___x_2897_; 
lean_dec_ref(v_type_2876_);
v___x_2897_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2896_, v___f_2892_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2897_) == 0)
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
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2897_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2897_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v___f_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; uint8_t v___x_2918_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v_a_2922_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v_a_2937_; 
v___f_2914_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2914_, 0, v_type_2876_);
v___x_2915_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_2916_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2917_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2918_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2884_, v_options_2883_, v___x_2917_);
if (v___x_2918_ == 0)
{
lean_object* v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = l_Lean_trace_profiler;
v___x_2988_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2883_, v___x_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; 
lean_dec_ref(v___f_2914_);
v___x_2989_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2896_, v___f_2892_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2989_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2989_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v_a_2998_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2989_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2989_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
goto v___jp_2946_;
}
}
else
{
goto v___jp_2946_;
}
v___jp_2919_:
{
lean_object* v___x_2923_; double v___x_2924_; double v___x_2925_; double v___x_2926_; double v___x_2927_; double v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2923_ = lean_io_mono_nanos_now();
v___x_2924_ = lean_float_of_nat(v___y_2920_);
v___x_2925_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2926_ = lean_float_div(v___x_2924_, v___x_2925_);
v___x_2927_ = lean_float_of_nat(v___x_2923_);
v___x_2928_ = lean_float_div(v___x_2927_, v___x_2925_);
v___x_2929_ = lean_box_float(v___x_2926_);
v___x_2930_ = lean_box_float(v___x_2928_);
v___x_2931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2929_);
lean_ctor_set(v___x_2931_, 1, v___x_2930_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v_a_2922_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2915_, v_hasTrace_2885_, v___x_2916_, v_options_2883_, v___x_2918_, v___y_2921_, v___f_2914_, v___x_2932_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
return v___x_2933_;
}
v___jp_2934_:
{
lean_object* v___x_2938_; double v___x_2939_; double v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2938_ = lean_io_get_num_heartbeats();
v___x_2939_ = lean_float_of_nat(v___y_2935_);
v___x_2940_ = lean_float_of_nat(v___x_2938_);
v___x_2941_ = lean_box_float(v___x_2939_);
v___x_2942_ = lean_box_float(v___x_2940_);
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2942_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v_a_2937_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2915_, v_hasTrace_2885_, v___x_2916_, v_options_2883_, v___x_2918_, v___y_2936_, v___f_2914_, v___x_2944_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
return v___x_2945_;
}
v___jp_2946_:
{
lean_object* v___x_2947_; lean_object* v_a_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2947_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2880_);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref(v___x_2947_);
v___x_2949_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2950_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2883_, v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_io_mono_nanos_now();
v___x_2952_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2896_, v___f_2892_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2952_) == 0)
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
lean_ctor_set_tag(v___x_2955_, 1);
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
v___y_2920_ = v___x_2951_;
v___y_2921_ = v_a_2948_;
v_a_2922_ = v___x_2958_;
goto v___jp_2919_;
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v_a_2961_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2952_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2952_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 0);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
v___y_2920_ = v___x_2951_;
v___y_2921_ = v_a_2948_;
v_a_2922_ = v___x_2966_;
goto v___jp_2919_;
}
}
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_io_get_num_heartbeats();
v___x_2970_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2896_, v___f_2892_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 1);
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
v___y_2935_ = v___x_2969_;
v___y_2936_ = v_a_2948_;
v_a_2937_ = v___x_2976_;
goto v___jp_2934_;
}
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v_a_2979_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2970_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2970_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set_tag(v___x_2981_, 0);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
v___y_2935_ = v___x_2969_;
v___y_2936_ = v_a_2948_;
v_a_2937_ = v___x_2984_;
goto v___jp_2934_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3006_, lean_object* v_type_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3006_, v_type_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
return v_res_3013_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_3014_, lean_object* v_n_3015_, lean_object* v_x_3016_){
_start:
{
uint8_t v___x_3017_; 
v___x_3017_ = l_Lean_Environment_hasExposedBody(v_env_3014_, v_n_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_env_3018_, lean_object* v_n_3019_, lean_object* v_x_3020_){
_start:
{
uint8_t v_res_3021_; lean_object* v_r_3022_; 
v_res_3021_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(v_env_3018_, v_n_3019_, v_x_3020_);
lean_dec_ref(v_x_3020_);
v_r_3022_ = lean_box(v_res_3021_);
return v_r_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3023_, lean_object* v_x_3024_){
_start:
{
if (lean_obj_tag(v_x_3024_) == 0)
{
lean_object* v_k_3025_; lean_object* v_v_3026_; lean_object* v_l_3027_; lean_object* v_r_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_k_3025_ = lean_ctor_get(v_x_3024_, 1);
v_v_3026_ = lean_ctor_get(v_x_3024_, 2);
v_l_3027_ = lean_ctor_get(v_x_3024_, 3);
v_r_3028_ = lean_ctor_get(v_x_3024_, 4);
v___x_3029_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3023_, v_l_3027_);
lean_inc(v_v_3026_);
lean_inc(v_k_3025_);
v___x_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3030_, 0, v_k_3025_);
lean_ctor_set(v___x_3030_, 1, v_v_3026_);
v___x_3031_ = lean_array_push(v___x_3029_, v___x_3030_);
v_init_3023_ = v___x_3031_;
v_x_3024_ = v_r_3028_;
goto _start;
}
else
{
return v_init_3023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3033_, lean_object* v_x_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3033_, v_x_3034_);
lean_dec(v_x_3034_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_3038_, lean_object* v_s_3039_){
_start:
{
lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v_all_3042_; lean_object* v___x_3043_; lean_object* v_exported_3044_; lean_object* v___x_3045_; 
v___f_3040_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3040_, 0, v_env_3038_);
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v_all_3042_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_3041_, v_s_3039_);
v___x_3043_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3040_, v_s_3039_);
v_exported_3044_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_3041_, v___x_3043_);
lean_dec(v___x_3043_);
lean_inc_ref(v_exported_3044_);
v___x_3045_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3045_, 0, v_exported_3044_);
lean_ctor_set(v___x_3045_, 1, v_exported_3044_);
lean_ctor_set(v___x_3045_, 2, v_all_3042_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; 
v___f_3058_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3061_ = 1;
v___x_3062_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3059_, v___x_3060_, v___x_3061_, v___f_3058_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_();
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0(lean_object* v_init_3065_, lean_object* v_t_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3065_, v_t_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3068_, lean_object* v_t_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0(v_init_3068_, v_t_3069_);
lean_dec(v_t_3069_);
return v_res_3070_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
lean_ctor_set(v___x_3074_, 1, v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3075_, lean_object* v_declNames_3076_, lean_object* v_recArgPos_3077_, lean_object* v_fixedParamPerms_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_){
_start:
{
lean_object* v_levelParams_3082_; lean_object* v_declName_3083_; lean_object* v_type_3084_; lean_object* v_value_3085_; lean_object* v___x_3086_; 
v_levelParams_3082_ = lean_ctor_get(v_preDef_3075_, 1);
lean_inc(v_levelParams_3082_);
v_declName_3083_ = lean_ctor_get(v_preDef_3075_, 3);
lean_inc_n(v_declName_3083_, 2);
v_type_3084_ = lean_ctor_get(v_preDef_3075_, 6);
lean_inc_ref(v_type_3084_);
v_value_3085_ = lean_ctor_get(v_preDef_3075_, 7);
lean_inc_ref(v_value_3085_);
lean_dec_ref(v_preDef_3075_);
v___x_3086_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3083_, v_a_3079_, v_a_3080_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3118_; 
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v___x_3086_, 0);
lean_dec(v_unused_3119_);
v___x_3088_ = v___x_3086_;
v_isShared_3089_ = v_isSharedCheck_3118_;
goto v_resetjp_3087_;
}
else
{
lean_dec(v___x_3086_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3118_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v_env_3091_; lean_object* v_nextMacroScope_3092_; lean_object* v_ngen_3093_; lean_object* v_auxDeclNGen_3094_; lean_object* v_traceState_3095_; lean_object* v_recordedDeps_3096_; lean_object* v_messages_3097_; lean_object* v_infoState_3098_; lean_object* v_snapshotTasks_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3116_; 
v___x_3090_ = lean_st_ref_take(v_a_3080_);
v_env_3091_ = lean_ctor_get(v___x_3090_, 0);
v_nextMacroScope_3092_ = lean_ctor_get(v___x_3090_, 1);
v_ngen_3093_ = lean_ctor_get(v___x_3090_, 2);
v_auxDeclNGen_3094_ = lean_ctor_get(v___x_3090_, 3);
v_traceState_3095_ = lean_ctor_get(v___x_3090_, 4);
v_recordedDeps_3096_ = lean_ctor_get(v___x_3090_, 6);
v_messages_3097_ = lean_ctor_get(v___x_3090_, 7);
v_infoState_3098_ = lean_ctor_get(v___x_3090_, 8);
v_snapshotTasks_3099_ = lean_ctor_get(v___x_3090_, 9);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v___x_3090_, 5);
lean_dec(v_unused_3117_);
v___x_3101_ = v___x_3090_;
v_isShared_3102_ = v_isSharedCheck_3116_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snapshotTasks_3099_);
lean_inc(v_infoState_3098_);
lean_inc(v_messages_3097_);
lean_inc(v_recordedDeps_3096_);
lean_inc(v_traceState_3095_);
lean_inc(v_auxDeclNGen_3094_);
lean_inc(v_ngen_3093_);
lean_inc(v_nextMacroScope_3092_);
lean_inc(v_env_3091_);
lean_dec(v___x_3090_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3116_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; 
v___x_3103_ = lean_box(0);
v___x_3104_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3083_);
v___x_3105_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3105_, 0, v_declName_3083_);
lean_ctor_set(v___x_3105_, 1, v_levelParams_3082_);
lean_ctor_set(v___x_3105_, 2, v_type_3084_);
lean_ctor_set(v___x_3105_, 3, v_value_3085_);
lean_ctor_set(v___x_3105_, 4, v_recArgPos_3077_);
lean_ctor_set(v___x_3105_, 5, v_declNames_3076_);
lean_ctor_set(v___x_3105_, 6, v_fixedParamPerms_3078_);
v___x_3106_ = 0;
v___x_3107_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3104_, v_env_3091_, v_declName_3083_, v___x_3105_, v___x_3106_);
v___x_3108_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 5, v___x_3108_);
lean_ctor_set(v___x_3101_, 0, v___x_3107_);
v___x_3110_ = v___x_3101_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_nextMacroScope_3092_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_ngen_3093_);
lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_auxDeclNGen_3094_);
lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_traceState_3095_);
lean_ctor_set(v_reuseFailAlloc_3115_, 5, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3115_, 6, v_recordedDeps_3096_);
lean_ctor_set(v_reuseFailAlloc_3115_, 7, v_messages_3097_);
lean_ctor_set(v_reuseFailAlloc_3115_, 8, v_infoState_3098_);
lean_ctor_set(v_reuseFailAlloc_3115_, 9, v_snapshotTasks_3099_);
v___x_3110_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = lean_st_ref_put(v_a_3080_, v___x_3110_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3103_);
v___x_3113_ = v___x_3088_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3103_);
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
}
else
{
lean_dec_ref(v_value_3085_);
lean_dec_ref(v_type_3084_);
lean_dec(v_declName_3083_);
lean_dec(v_levelParams_3082_);
lean_dec_ref(v_fixedParamPerms_3078_);
lean_dec(v_recArgPos_3077_);
lean_dec_ref(v_declNames_3076_);
return v___x_3086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3120_, lean_object* v_declNames_3121_, lean_object* v_recArgPos_3122_, lean_object* v_fixedParamPerms_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3120_, v_declNames_3121_, v_recArgPos_3122_, v_fixedParamPerms_3123_, v_a_3124_, v_a_3125_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(lean_object* v_e_3128_, lean_object* v_k_3129_, uint8_t v_cleanupAnnotations_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___f_3136_; uint8_t v___x_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3136_, 0, v_k_3129_);
v___x_3137_ = 1;
v___x_3138_ = 0;
v___x_3139_ = lean_box(0);
v___x_3140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3128_, v___x_3137_, v___x_3138_, v___x_3137_, v___x_3138_, v___x_3139_, v___f_3136_, v_cleanupAnnotations_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_a_3149_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3140_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3140_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg___boxed(lean_object* v_e_3157_, lean_object* v_k_3158_, lean_object* v_cleanupAnnotations_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3165_; lean_object* v_res_3166_; 
v_cleanupAnnotations_boxed_3165_ = lean_unbox(v_cleanupAnnotations_3159_);
v_res_3166_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_e_3157_, v_k_3158_, v_cleanupAnnotations_boxed_3165_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_00_u03b1_3167_, lean_object* v_e_3168_, lean_object* v_k_3169_, uint8_t v_cleanupAnnotations_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_e_3168_, v_k_3169_, v_cleanupAnnotations_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_00_u03b1_3177_, lean_object* v_e_3178_, lean_object* v_k_3179_, lean_object* v_cleanupAnnotations_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3186_; lean_object* v_res_3187_; 
v_cleanupAnnotations_boxed_3186_ = lean_unbox(v_cleanupAnnotations_3180_);
v_res_3187_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_00_u03b1_3177_, v_e_3178_, v_k_3179_, v_cleanupAnnotations_boxed_3186_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3188_, uint8_t v_isExporting_3189_, lean_object* v___x_3190_, lean_object* v___y_3191_, lean_object* v___x_3192_, lean_object* v_a_x3f_3193_){
_start:
{
lean_object* v___x_3195_; lean_object* v_env_3196_; lean_object* v_nextMacroScope_3197_; lean_object* v_ngen_3198_; lean_object* v_auxDeclNGen_3199_; lean_object* v_traceState_3200_; lean_object* v_recordedDeps_3201_; lean_object* v_messages_3202_; lean_object* v_infoState_3203_; lean_object* v_snapshotTasks_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3229_; 
v___x_3195_ = lean_st_ref_take(v___y_3188_);
v_env_3196_ = lean_ctor_get(v___x_3195_, 0);
v_nextMacroScope_3197_ = lean_ctor_get(v___x_3195_, 1);
v_ngen_3198_ = lean_ctor_get(v___x_3195_, 2);
v_auxDeclNGen_3199_ = lean_ctor_get(v___x_3195_, 3);
v_traceState_3200_ = lean_ctor_get(v___x_3195_, 4);
v_recordedDeps_3201_ = lean_ctor_get(v___x_3195_, 6);
v_messages_3202_ = lean_ctor_get(v___x_3195_, 7);
v_infoState_3203_ = lean_ctor_get(v___x_3195_, 8);
v_snapshotTasks_3204_ = lean_ctor_get(v___x_3195_, 9);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3229_ == 0)
{
lean_object* v_unused_3230_; 
v_unused_3230_ = lean_ctor_get(v___x_3195_, 5);
lean_dec(v_unused_3230_);
v___x_3206_ = v___x_3195_;
v_isShared_3207_ = v_isSharedCheck_3229_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_snapshotTasks_3204_);
lean_inc(v_infoState_3203_);
lean_inc(v_messages_3202_);
lean_inc(v_recordedDeps_3201_);
lean_inc(v_traceState_3200_);
lean_inc(v_auxDeclNGen_3199_);
lean_inc(v_ngen_3198_);
lean_inc(v_nextMacroScope_3197_);
lean_inc(v_env_3196_);
lean_dec(v___x_3195_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3229_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3210_; 
v___x_3208_ = l_Lean_Environment_setExporting(v_env_3196_, v_isExporting_3189_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 5, v___x_3190_);
lean_ctor_set(v___x_3206_, 0, v___x_3208_);
v___x_3210_ = v___x_3206_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3208_);
lean_ctor_set(v_reuseFailAlloc_3228_, 1, v_nextMacroScope_3197_);
lean_ctor_set(v_reuseFailAlloc_3228_, 2, v_ngen_3198_);
lean_ctor_set(v_reuseFailAlloc_3228_, 3, v_auxDeclNGen_3199_);
lean_ctor_set(v_reuseFailAlloc_3228_, 4, v_traceState_3200_);
lean_ctor_set(v_reuseFailAlloc_3228_, 5, v___x_3190_);
lean_ctor_set(v_reuseFailAlloc_3228_, 6, v_recordedDeps_3201_);
lean_ctor_set(v_reuseFailAlloc_3228_, 7, v_messages_3202_);
lean_ctor_set(v_reuseFailAlloc_3228_, 8, v_infoState_3203_);
lean_ctor_set(v_reuseFailAlloc_3228_, 9, v_snapshotTasks_3204_);
v___x_3210_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v_mctx_3213_; lean_object* v_zetaDeltaFVarIds_3214_; lean_object* v_postponed_3215_; lean_object* v_diag_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3226_; 
v___x_3211_ = lean_st_ref_put(v___y_3188_, v___x_3210_);
v___x_3212_ = lean_st_ref_take(v___y_3191_);
v_mctx_3213_ = lean_ctor_get(v___x_3212_, 0);
v_zetaDeltaFVarIds_3214_ = lean_ctor_get(v___x_3212_, 2);
v_postponed_3215_ = lean_ctor_get(v___x_3212_, 3);
v_diag_3216_ = lean_ctor_get(v___x_3212_, 4);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v___x_3212_, 1);
lean_dec(v_unused_3227_);
v___x_3218_ = v___x_3212_;
v_isShared_3219_ = v_isSharedCheck_3226_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_diag_3216_);
lean_inc(v_postponed_3215_);
lean_inc(v_zetaDeltaFVarIds_3214_);
lean_inc(v_mctx_3213_);
lean_dec(v___x_3212_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3226_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3220_ = lean_box(0);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 1, v___x_3192_);
v___x_3222_ = v___x_3218_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_mctx_3213_);
lean_ctor_set(v_reuseFailAlloc_3225_, 1, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3225_, 2, v_zetaDeltaFVarIds_3214_);
lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_postponed_3215_);
lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_diag_3216_);
v___x_3222_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_st_ref_put(v___y_3191_, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3220_);
return v___x_3224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3231_, lean_object* v_isExporting_3232_, lean_object* v___x_3233_, lean_object* v___y_3234_, lean_object* v___x_3235_, lean_object* v_a_x3f_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_isExporting_boxed_3238_; lean_object* v_res_3239_; 
v_isExporting_boxed_3238_ = lean_unbox(v_isExporting_3232_);
v_res_3239_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3231_, v_isExporting_boxed_3238_, v___x_3233_, v___y_3234_, v___x_3235_, v_a_x3f_3236_);
lean_dec(v_a_x3f_3236_);
lean_dec(v___y_3234_);
lean_dec(v___y_3231_);
return v_res_3239_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3241_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
lean_ctor_set(v___x_3241_, 2, v___x_3240_);
lean_ctor_set(v___x_3241_, 3, v___x_3240_);
lean_ctor_set(v___x_3241_, 4, v___x_3240_);
lean_ctor_set(v___x_3241_, 5, v___x_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3242_, uint8_t v_isExporting_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v___x_3249_; lean_object* v_env_3250_; lean_object* v___x_3251_; uint8_t v_isModule_3252_; 
v___x_3249_ = lean_st_ref_get(v___y_3247_);
v_env_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc_ref(v_env_3250_);
lean_dec(v___x_3249_);
v___x_3251_ = l_Lean_Environment_header(v_env_3250_);
v_isModule_3252_ = lean_ctor_get_uint8(v___x_3251_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3251_);
if (v_isModule_3252_ == 0)
{
lean_object* v___x_3253_; 
lean_dec_ref(v_env_3250_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
v___x_3253_ = lean_apply_5(v_x_3242_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, lean_box(0));
return v___x_3253_;
}
else
{
uint8_t v_isExporting_3254_; 
v_isExporting_3254_ = lean_ctor_get_uint8(v_env_3250_, sizeof(void*)*13);
lean_dec_ref(v_env_3250_);
if (v_isExporting_3243_ == 0)
{
if (v_isExporting_3254_ == 0)
{
lean_object* v___x_3321_; 
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
v___x_3321_ = lean_apply_5(v_x_3242_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, lean_box(0));
return v___x_3321_;
}
else
{
goto v___jp_3255_;
}
}
else
{
if (v_isExporting_3254_ == 0)
{
goto v___jp_3255_;
}
else
{
lean_object* v___x_3322_; 
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
v___x_3322_ = lean_apply_5(v_x_3242_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, lean_box(0));
return v___x_3322_;
}
}
v___jp_3255_:
{
lean_object* v___x_3256_; lean_object* v_env_3257_; lean_object* v_nextMacroScope_3258_; lean_object* v_ngen_3259_; lean_object* v_auxDeclNGen_3260_; lean_object* v_traceState_3261_; lean_object* v_recordedDeps_3262_; lean_object* v_messages_3263_; lean_object* v_infoState_3264_; lean_object* v_snapshotTasks_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3319_; 
v___x_3256_ = lean_st_ref_take(v___y_3247_);
v_env_3257_ = lean_ctor_get(v___x_3256_, 0);
v_nextMacroScope_3258_ = lean_ctor_get(v___x_3256_, 1);
v_ngen_3259_ = lean_ctor_get(v___x_3256_, 2);
v_auxDeclNGen_3260_ = lean_ctor_get(v___x_3256_, 3);
v_traceState_3261_ = lean_ctor_get(v___x_3256_, 4);
v_recordedDeps_3262_ = lean_ctor_get(v___x_3256_, 6);
v_messages_3263_ = lean_ctor_get(v___x_3256_, 7);
v_infoState_3264_ = lean_ctor_get(v___x_3256_, 8);
v_snapshotTasks_3265_ = lean_ctor_get(v___x_3256_, 9);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3319_ == 0)
{
lean_object* v_unused_3320_; 
v_unused_3320_ = lean_ctor_get(v___x_3256_, 5);
lean_dec(v_unused_3320_);
v___x_3267_ = v___x_3256_;
v_isShared_3268_ = v_isSharedCheck_3319_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_snapshotTasks_3265_);
lean_inc(v_infoState_3264_);
lean_inc(v_messages_3263_);
lean_inc(v_recordedDeps_3262_);
lean_inc(v_traceState_3261_);
lean_inc(v_auxDeclNGen_3260_);
lean_inc(v_ngen_3259_);
lean_inc(v_nextMacroScope_3258_);
lean_inc(v_env_3257_);
lean_dec(v___x_3256_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3319_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3269_ = l_Lean_Environment_setExporting(v_env_3257_, v_isExporting_3243_);
v___x_3270_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 5, v___x_3270_);
lean_ctor_set(v___x_3267_, 0, v___x_3269_);
v___x_3272_ = v___x_3267_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3269_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_nextMacroScope_3258_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_ngen_3259_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_auxDeclNGen_3260_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v_traceState_3261_);
lean_ctor_set(v_reuseFailAlloc_3318_, 5, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3318_, 6, v_recordedDeps_3262_);
lean_ctor_set(v_reuseFailAlloc_3318_, 7, v_messages_3263_);
lean_ctor_set(v_reuseFailAlloc_3318_, 8, v_infoState_3264_);
lean_ctor_set(v_reuseFailAlloc_3318_, 9, v_snapshotTasks_3265_);
v___x_3272_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v_mctx_3275_; lean_object* v_zetaDeltaFVarIds_3276_; lean_object* v_postponed_3277_; lean_object* v_diag_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3316_; 
v___x_3273_ = lean_st_ref_put(v___y_3247_, v___x_3272_);
v___x_3274_ = lean_st_ref_take(v___y_3245_);
v_mctx_3275_ = lean_ctor_get(v___x_3274_, 0);
v_zetaDeltaFVarIds_3276_ = lean_ctor_get(v___x_3274_, 2);
v_postponed_3277_ = lean_ctor_get(v___x_3274_, 3);
v_diag_3278_ = lean_ctor_get(v___x_3274_, 4);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; 
v_unused_3317_ = lean_ctor_get(v___x_3274_, 1);
lean_dec(v_unused_3317_);
v___x_3280_ = v___x_3274_;
v_isShared_3281_ = v_isSharedCheck_3316_;
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
v_isShared_3281_ = v_isSharedCheck_3316_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v___x_3284_; 
v___x_3282_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 1, v___x_3282_);
v___x_3284_ = v___x_3280_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_mctx_3275_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___x_3282_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_zetaDeltaFVarIds_3276_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v_postponed_3277_);
lean_ctor_set(v_reuseFailAlloc_3315_, 4, v_diag_3278_);
v___x_3284_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
lean_object* v___x_3285_; lean_object* v_r_3286_; 
v___x_3285_ = lean_st_ref_put(v___y_3245_, v___x_3284_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
v_r_3286_ = lean_apply_5(v_x_3242_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, lean_box(0));
if (lean_obj_tag(v_r_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3303_; 
v_a_3287_ = lean_ctor_get(v_r_3286_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_r_3286_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3289_ = v_r_3286_;
v_isShared_3290_ = v_isSharedCheck_3303_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v_r_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3303_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
lean_inc(v_a_3287_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 1);
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
v___x_3293_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3247_, v_isExporting_3254_, v___x_3270_, v___y_3245_, v___x_3282_, v___x_3292_);
lean_dec_ref(v___x_3292_);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3300_ == 0)
{
lean_object* v_unused_3301_; 
v_unused_3301_ = lean_ctor_get(v___x_3293_, 0);
lean_dec(v_unused_3301_);
v___x_3295_ = v___x_3293_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_dec(v___x_3293_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
lean_ctor_set(v___x_3295_, 0, v_a_3287_);
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3287_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
v_a_3304_ = lean_ctor_get(v_r_3286_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v_r_3286_, 1);
v___x_3305_ = lean_box(0);
v___x_3306_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3247_, v_isExporting_3254_, v___x_3270_, v___y_3245_, v___x_3282_, v___x_3305_);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; 
v_unused_3314_ = lean_ctor_get(v___x_3306_, 0);
lean_dec(v_unused_3314_);
v___x_3308_ = v___x_3306_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_dec(v___x_3306_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set_tag(v___x_3308_, 1);
lean_ctor_set(v___x_3308_, 0, v_a_3304_);
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3304_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3323_, lean_object* v_isExporting_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v_isExporting_boxed_3330_; lean_object* v_res_3331_; 
v_isExporting_boxed_3330_ = lean_unbox(v_isExporting_3324_);
v_res_3331_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3323_, v_isExporting_boxed_3330_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3332_, uint8_t v_when_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
if (v_when_3333_ == 0)
{
lean_object* v___x_3339_; 
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
v___x_3339_ = lean_apply_5(v_x_3332_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, lean_box(0));
return v___x_3339_;
}
else
{
uint8_t v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = 0;
v___x_3341_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3332_, v___x_3340_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3342_, lean_object* v_when_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
uint8_t v_when_boxed_3349_; lean_object* v_res_3350_; 
v_when_boxed_3349_ = lean_unbox(v_when_3343_);
v_res_3350_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3342_, v_when_boxed_3349_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec(v___y_3345_);
lean_dec_ref(v___y_3344_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
if (lean_obj_tag(v_a_3351_) == 0)
{
lean_object* v___x_3353_; 
v___x_3353_ = l_List_reverse___redArg(v_a_3352_);
return v___x_3353_;
}
else
{
lean_object* v_head_3354_; lean_object* v_tail_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3364_; 
v_head_3354_ = lean_ctor_get(v_a_3351_, 0);
v_tail_3355_ = lean_ctor_get(v_a_3351_, 1);
v_isSharedCheck_3364_ = !lean_is_exclusive(v_a_3351_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3357_ = v_a_3351_;
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_tail_3355_);
lean_inc(v_head_3354_);
lean_dec(v_a_3351_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3364_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; lean_object* v___x_3361_; 
v___x_3359_ = l_Lean_mkLevelParam(v_head_3354_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 1, v_a_3352_);
lean_ctor_set(v___x_3357_, 0, v___x_3359_);
v___x_3361_ = v___x_3357_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_a_3352_);
v___x_3361_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
v_a_3351_ = v_tail_3355_;
v_a_3352_ = v___x_3361_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3365_, lean_object* v_declName_3366_, lean_object* v_name_3367_, lean_object* v_xs_3368_, lean_object* v_body_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v___x_3375_; lean_object* v_us_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3375_ = lean_box(0);
lean_inc(v_levelParams_3365_);
v_us_3376_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3365_, v___x_3375_);
lean_inc(v_declName_3366_);
v___x_3377_ = l_Lean_mkConst(v_declName_3366_, v_us_3376_);
v___x_3378_ = l_Lean_mkAppN(v___x_3377_, v_xs_3368_);
v___x_3379_ = l_Lean_Meta_mkEq(v___x_3378_, v_body_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc_n(v_a_3380_, 2);
lean_dec_ref_known(v___x_3379_, 1);
v___x_3381_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3381_, 0, v_declName_3366_);
lean_closure_set(v___x_3381_, 1, v_a_3380_);
v___x_3382_ = 1;
v___x_3383_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3381_, v___x_3382_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; uint8_t v___x_3385_; uint8_t v___x_3386_; lean_object* v___x_3387_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3383_, 1);
v___x_3385_ = 0;
v___x_3386_ = 1;
v___x_3387_ = l_Lean_Meta_mkForallFVars(v_xs_3368_, v_a_3380_, v___x_3385_, v___x_3382_, v___x_3382_, v___x_3386_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v___x_3389_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3387_, 1);
v___x_3389_ = l_Lean_Meta_letToHave(v_a_3388_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v___x_3389_, 1);
v___x_3391_ = l_Lean_Meta_mkLambdaFVars(v_xs_3368_, v_a_3384_, v___x_3385_, v___x_3382_, v___x_3385_, v___x_3382_, v___x_3386_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
lean_inc_n(v_name_3367_, 2);
v___x_3393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3393_, 0, v_name_3367_);
lean_ctor_set(v___x_3393_, 1, v_levelParams_3365_);
lean_ctor_set(v___x_3393_, 2, v_a_3390_);
v___x_3394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_name_3367_);
lean_ctor_set(v___x_3394_, 1, v___x_3375_);
v___x_3395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v_a_3392_);
lean_ctor_set(v___x_3395_, 2, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
v___x_3397_ = l_Lean_addDecl(v___x_3396_, v___x_3385_, v___y_3372_, v___y_3373_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v___x_3398_; 
lean_dec_ref_known(v___x_3397_, 1);
v___x_3398_ = l_Lean_inferDefEqAttr(v_name_3367_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
return v___x_3398_;
}
else
{
lean_dec(v_name_3367_);
return v___x_3397_;
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec(v_a_3390_);
lean_dec(v_name_3367_);
lean_dec(v_levelParams_3365_);
v_a_3399_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3391_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3391_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec(v_a_3384_);
lean_dec(v_name_3367_);
lean_dec(v_levelParams_3365_);
v_a_3407_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3389_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3389_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec(v_a_3384_);
lean_dec(v_name_3367_);
lean_dec(v_levelParams_3365_);
v_a_3415_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3387_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3387_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v_a_3380_);
lean_dec(v_name_3367_);
lean_dec(v_levelParams_3365_);
v_a_3423_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3383_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3383_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
else
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
lean_dec(v_name_3367_);
lean_dec(v_declName_3366_);
lean_dec(v_levelParams_3365_);
v_a_3431_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3433_ = v___x_3379_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3379_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3439_, lean_object* v_declName_3440_, lean_object* v_name_3441_, lean_object* v_xs_3442_, lean_object* v_body_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3439_, v_declName_3440_, v_name_3441_, v_xs_3442_, v_body_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec_ref(v_xs_3442_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(lean_object* v_o_3450_, lean_object* v_k_3451_, uint8_t v_v_3452_){
_start:
{
lean_object* v_map_3453_; uint8_t v_hasTrace_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3468_; 
v_map_3453_ = lean_ctor_get(v_o_3450_, 0);
v_hasTrace_3454_ = lean_ctor_get_uint8(v_o_3450_, sizeof(void*)*1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_o_3450_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3456_ = v_o_3450_;
v_isShared_3457_ = v_isSharedCheck_3468_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_map_3453_);
lean_dec(v_o_3450_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3468_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3458_, 0, v_v_3452_);
lean_inc(v_k_3451_);
v___x_3459_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3451_, v___x_3458_, v_map_3453_);
if (v_hasTrace_3454_ == 0)
{
lean_object* v___x_3460_; uint8_t v___x_3461_; lean_object* v___x_3463_; 
v___x_3460_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3461_ = l_Lean_Name_isPrefixOf(v___x_3460_, v_k_3451_);
lean_dec(v_k_3451_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3459_);
v___x_3463_ = v___x_3456_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3459_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*1, v___x_3461_);
return v___x_3463_;
}
}
else
{
lean_object* v___x_3466_; 
lean_dec(v_k_3451_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3459_);
v___x_3466_ = v___x_3456_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3459_);
lean_ctor_set_uint8(v_reuseFailAlloc_3467_, sizeof(void*)*1, v_hasTrace_3454_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4___boxed(lean_object* v_o_3469_, lean_object* v_k_3470_, lean_object* v_v_3471_){
_start:
{
uint8_t v_v_boxed_3472_; lean_object* v_res_3473_; 
v_v_boxed_3472_ = lean_unbox(v_v_3471_);
v_res_3473_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(v_o_3469_, v_k_3470_, v_v_boxed_3472_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_3474_, lean_object* v_opt_3475_, uint8_t v_val_3476_){
_start:
{
lean_object* v_name_3477_; lean_object* v___x_3478_; 
v_name_3477_ = lean_ctor_get(v_opt_3475_, 0);
lean_inc(v_name_3477_);
lean_dec_ref(v_opt_3475_);
v___x_3478_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(v_opts_3474_, v_name_3477_, v_val_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_3479_, lean_object* v_opt_3480_, lean_object* v_val_3481_){
_start:
{
uint8_t v_val_boxed_3482_; lean_object* v_res_3483_; 
v_val_boxed_3482_ = lean_unbox(v_val_3481_);
v_res_3483_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_opts_3479_, v_opt_3480_, v_val_boxed_3482_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3484_, lean_object* v_info_3485_, lean_object* v_name_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_toCold_3492_; lean_object* v_levelParams_3493_; lean_object* v_value_3494_; lean_object* v_currRecDepth_3495_; lean_object* v_ref_3496_; uint8_t v_suppressElabErrors_3497_; uint8_t v_isRecordingDeps_3498_; lean_object* v_fileName_3499_; lean_object* v_fileMap_3500_; lean_object* v_options_3501_; lean_object* v_currNamespace_3502_; lean_object* v_openDecls_3503_; lean_object* v_initHeartbeats_3504_; lean_object* v_maxHeartbeats_3505_; lean_object* v_quotContext_3506_; lean_object* v_currMacroScope_3507_; lean_object* v_cancelTk_x3f_3508_; lean_object* v_inheritedTraceOptions_3509_; lean_object* v___f_3510_; uint8_t v___x_3511_; lean_object* v___y_3513_; uint16_t v___y_3514_; lean_object* v_fileName_3515_; lean_object* v_fileMap_3516_; lean_object* v_currNamespace_3517_; lean_object* v_openDecls_3518_; lean_object* v_initHeartbeats_3519_; lean_object* v_maxHeartbeats_3520_; lean_object* v_quotContext_3521_; lean_object* v_currMacroScope_3522_; lean_object* v_cancelTk_x3f_3523_; lean_object* v_inheritedTraceOptions_3524_; lean_object* v_currRecDepth_3525_; lean_object* v_ref_3526_; uint8_t v_suppressElabErrors_3527_; uint8_t v_isRecordingDeps_3528_; lean_object* v___y_3529_; uint8_t v___y_3536_; lean_object* v___y_3537_; uint16_t v___y_3538_; lean_object* v___y_3561_; 
v_toCold_3492_ = lean_ctor_get(v_a_3489_, 0);
v_levelParams_3493_ = lean_ctor_get(v_info_3485_, 1);
lean_inc(v_levelParams_3493_);
v_value_3494_ = lean_ctor_get(v_info_3485_, 3);
lean_inc_ref(v_value_3494_);
lean_dec_ref(v_info_3485_);
v_currRecDepth_3495_ = lean_ctor_get(v_a_3489_, 1);
v_ref_3496_ = lean_ctor_get(v_a_3489_, 2);
v_suppressElabErrors_3497_ = lean_ctor_get_uint8(v_a_3489_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3498_ = lean_ctor_get_uint8(v_a_3489_, sizeof(void*)*3 + 3);
v_fileName_3499_ = lean_ctor_get(v_toCold_3492_, 0);
v_fileMap_3500_ = lean_ctor_get(v_toCold_3492_, 1);
v_options_3501_ = lean_ctor_get(v_toCold_3492_, 2);
v_currNamespace_3502_ = lean_ctor_get(v_toCold_3492_, 4);
v_openDecls_3503_ = lean_ctor_get(v_toCold_3492_, 5);
v_initHeartbeats_3504_ = lean_ctor_get(v_toCold_3492_, 6);
v_maxHeartbeats_3505_ = lean_ctor_get(v_toCold_3492_, 7);
v_quotContext_3506_ = lean_ctor_get(v_toCold_3492_, 8);
v_currMacroScope_3507_ = lean_ctor_get(v_toCold_3492_, 9);
v_cancelTk_x3f_3508_ = lean_ctor_get(v_toCold_3492_, 10);
v_inheritedTraceOptions_3509_ = lean_ctor_get(v_toCold_3492_, 11);
v___f_3510_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3510_, 0, v_levelParams_3493_);
lean_closure_set(v___f_3510_, 1, v_declName_3484_);
lean_closure_set(v___f_3510_, 2, v_name_3486_);
v___x_3511_ = 0;
if (v_isRecordingDeps_3498_ == 0)
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3501_);
v___x_3572_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_options_3501_, v___x_3571_, v_isRecordingDeps_3498_);
v___y_3561_ = v___x_3572_;
goto v___jp_3560_;
}
else
{
lean_object* v___x_3573_; 
lean_inc_ref(v_options_3501_);
v___x_3573_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_3501_);
v___y_3561_ = v___x_3573_;
goto v___jp_3560_;
}
v___jp_3512_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3530_ = l_Lean_maxRecDepth;
v___x_3531_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___y_3513_, v___x_3530_);
v___x_3532_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3532_, 0, v_fileName_3515_);
lean_ctor_set(v___x_3532_, 1, v_fileMap_3516_);
lean_ctor_set(v___x_3532_, 2, v___y_3513_);
lean_ctor_set(v___x_3532_, 3, v___x_3531_);
lean_ctor_set(v___x_3532_, 4, v_currNamespace_3517_);
lean_ctor_set(v___x_3532_, 5, v_openDecls_3518_);
lean_ctor_set(v___x_3532_, 6, v_initHeartbeats_3519_);
lean_ctor_set(v___x_3532_, 7, v_maxHeartbeats_3520_);
lean_ctor_set(v___x_3532_, 8, v_quotContext_3521_);
lean_ctor_set(v___x_3532_, 9, v_currMacroScope_3522_);
lean_ctor_set(v___x_3532_, 10, v_cancelTk_x3f_3523_);
lean_ctor_set(v___x_3532_, 11, v_inheritedTraceOptions_3524_);
lean_inc(v_ref_3526_);
lean_inc(v_currRecDepth_3525_);
v___x_3533_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3533_, 0, v___x_3532_);
lean_ctor_set(v___x_3533_, 1, v_currRecDepth_3525_);
lean_ctor_set(v___x_3533_, 2, v_ref_3526_);
lean_ctor_set_uint16(v___x_3533_, sizeof(void*)*3, v___y_3514_);
lean_ctor_set_uint8(v___x_3533_, sizeof(void*)*3 + 2, v_suppressElabErrors_3527_);
lean_ctor_set_uint8(v___x_3533_, sizeof(void*)*3 + 3, v_isRecordingDeps_3528_);
v___x_3534_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_value_3494_, v___f_3510_, v___x_3511_, v_a_3487_, v_a_3488_, v___x_3533_, v___y_3529_);
lean_dec_ref_known(v___x_3533_, 3);
return v___x_3534_;
}
v___jp_3535_:
{
lean_object* v___x_3539_; lean_object* v_env_3540_; lean_object* v_nextMacroScope_3541_; lean_object* v_ngen_3542_; lean_object* v_auxDeclNGen_3543_; lean_object* v_traceState_3544_; lean_object* v_recordedDeps_3545_; lean_object* v_messages_3546_; lean_object* v_infoState_3547_; lean_object* v_snapshotTasks_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3558_; 
v___x_3539_ = lean_st_ref_take(v_a_3490_);
v_env_3540_ = lean_ctor_get(v___x_3539_, 0);
v_nextMacroScope_3541_ = lean_ctor_get(v___x_3539_, 1);
v_ngen_3542_ = lean_ctor_get(v___x_3539_, 2);
v_auxDeclNGen_3543_ = lean_ctor_get(v___x_3539_, 3);
v_traceState_3544_ = lean_ctor_get(v___x_3539_, 4);
v_recordedDeps_3545_ = lean_ctor_get(v___x_3539_, 6);
v_messages_3546_ = lean_ctor_get(v___x_3539_, 7);
v_infoState_3547_ = lean_ctor_get(v___x_3539_, 8);
v_snapshotTasks_3548_ = lean_ctor_get(v___x_3539_, 9);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3558_ == 0)
{
lean_object* v_unused_3559_; 
v_unused_3559_ = lean_ctor_get(v___x_3539_, 5);
lean_dec(v_unused_3559_);
v___x_3550_ = v___x_3539_;
v_isShared_3551_ = v_isSharedCheck_3558_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_snapshotTasks_3548_);
lean_inc(v_infoState_3547_);
lean_inc(v_messages_3546_);
lean_inc(v_recordedDeps_3545_);
lean_inc(v_traceState_3544_);
lean_inc(v_auxDeclNGen_3543_);
lean_inc(v_ngen_3542_);
lean_inc(v_nextMacroScope_3541_);
lean_inc(v_env_3540_);
lean_dec(v___x_3539_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3558_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3555_; 
v___x_3552_ = l_Lean_Kernel_enableDiag(v_env_3540_, v___y_3536_);
v___x_3553_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 5, v___x_3553_);
lean_ctor_set(v___x_3550_, 0, v___x_3552_);
v___x_3555_ = v___x_3550_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3552_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v_nextMacroScope_3541_);
lean_ctor_set(v_reuseFailAlloc_3557_, 2, v_ngen_3542_);
lean_ctor_set(v_reuseFailAlloc_3557_, 3, v_auxDeclNGen_3543_);
lean_ctor_set(v_reuseFailAlloc_3557_, 4, v_traceState_3544_);
lean_ctor_set(v_reuseFailAlloc_3557_, 5, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3557_, 6, v_recordedDeps_3545_);
lean_ctor_set(v_reuseFailAlloc_3557_, 7, v_messages_3546_);
lean_ctor_set(v_reuseFailAlloc_3557_, 8, v_infoState_3547_);
lean_ctor_set(v_reuseFailAlloc_3557_, 9, v_snapshotTasks_3548_);
v___x_3555_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_st_ref_put(v_a_3490_, v___x_3555_);
lean_inc_ref(v_inheritedTraceOptions_3509_);
lean_inc(v_cancelTk_x3f_3508_);
lean_inc(v_currMacroScope_3507_);
lean_inc(v_quotContext_3506_);
lean_inc(v_maxHeartbeats_3505_);
lean_inc(v_initHeartbeats_3504_);
lean_inc(v_openDecls_3503_);
lean_inc(v_currNamespace_3502_);
lean_inc_ref(v_fileMap_3500_);
lean_inc_ref(v_fileName_3499_);
v___y_3513_ = v___y_3537_;
v___y_3514_ = v___y_3538_;
v_fileName_3515_ = v_fileName_3499_;
v_fileMap_3516_ = v_fileMap_3500_;
v_currNamespace_3517_ = v_currNamespace_3502_;
v_openDecls_3518_ = v_openDecls_3503_;
v_initHeartbeats_3519_ = v_initHeartbeats_3504_;
v_maxHeartbeats_3520_ = v_maxHeartbeats_3505_;
v_quotContext_3521_ = v_quotContext_3506_;
v_currMacroScope_3522_ = v_currMacroScope_3507_;
v_cancelTk_x3f_3523_ = v_cancelTk_x3f_3508_;
v_inheritedTraceOptions_3524_ = v_inheritedTraceOptions_3509_;
v_currRecDepth_3525_ = v_currRecDepth_3495_;
v_ref_3526_ = v_ref_3496_;
v_suppressElabErrors_3527_ = v_suppressElabErrors_3497_;
v_isRecordingDeps_3528_ = v_isRecordingDeps_3498_;
v___y_3529_ = v_a_3490_;
goto v___jp_3512_;
}
}
}
v___jp_3560_:
{
uint16_t v___x_3562_; lean_object* v___x_3563_; lean_object* v_env_3564_; uint8_t v___x_3565_; uint16_t v___x_3566_; uint16_t v___x_3567_; uint16_t v___x_3568_; uint8_t v___x_3569_; 
v___x_3562_ = l_Lean_OptionFlags_ofOptions(v___y_3561_);
v___x_3563_ = lean_st_ref_get(v_a_3490_);
v_env_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc_ref(v_env_3564_);
lean_dec(v___x_3563_);
v___x_3565_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3564_);
lean_dec_ref(v_env_3564_);
v___x_3566_ = 512;
v___x_3567_ = lean_uint16_land(v___x_3562_, v___x_3566_);
v___x_3568_ = 0;
v___x_3569_ = lean_uint16_dec_eq(v___x_3567_, v___x_3568_);
if (v___x_3569_ == 0)
{
if (v___x_3565_ == 0)
{
uint8_t v___x_3570_; 
v___x_3570_ = 1;
v___y_3536_ = v___x_3570_;
v___y_3537_ = v___y_3561_;
v___y_3538_ = v___x_3562_;
goto v___jp_3535_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3509_);
lean_inc(v_cancelTk_x3f_3508_);
lean_inc(v_currMacroScope_3507_);
lean_inc(v_quotContext_3506_);
lean_inc(v_maxHeartbeats_3505_);
lean_inc(v_initHeartbeats_3504_);
lean_inc(v_openDecls_3503_);
lean_inc(v_currNamespace_3502_);
lean_inc_ref(v_fileMap_3500_);
lean_inc_ref(v_fileName_3499_);
v___y_3513_ = v___y_3561_;
v___y_3514_ = v___x_3562_;
v_fileName_3515_ = v_fileName_3499_;
v_fileMap_3516_ = v_fileMap_3500_;
v_currNamespace_3517_ = v_currNamespace_3502_;
v_openDecls_3518_ = v_openDecls_3503_;
v_initHeartbeats_3519_ = v_initHeartbeats_3504_;
v_maxHeartbeats_3520_ = v_maxHeartbeats_3505_;
v_quotContext_3521_ = v_quotContext_3506_;
v_currMacroScope_3522_ = v_currMacroScope_3507_;
v_cancelTk_x3f_3523_ = v_cancelTk_x3f_3508_;
v_inheritedTraceOptions_3524_ = v_inheritedTraceOptions_3509_;
v_currRecDepth_3525_ = v_currRecDepth_3495_;
v_ref_3526_ = v_ref_3496_;
v_suppressElabErrors_3527_ = v_suppressElabErrors_3497_;
v_isRecordingDeps_3528_ = v_isRecordingDeps_3498_;
v___y_3529_ = v_a_3490_;
goto v___jp_3512_;
}
}
else
{
if (v___x_3565_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3509_);
lean_inc(v_cancelTk_x3f_3508_);
lean_inc(v_currMacroScope_3507_);
lean_inc(v_quotContext_3506_);
lean_inc(v_maxHeartbeats_3505_);
lean_inc(v_initHeartbeats_3504_);
lean_inc(v_openDecls_3503_);
lean_inc(v_currNamespace_3502_);
lean_inc_ref(v_fileMap_3500_);
lean_inc_ref(v_fileName_3499_);
v___y_3513_ = v___y_3561_;
v___y_3514_ = v___x_3562_;
v_fileName_3515_ = v_fileName_3499_;
v_fileMap_3516_ = v_fileMap_3500_;
v_currNamespace_3517_ = v_currNamespace_3502_;
v_openDecls_3518_ = v_openDecls_3503_;
v_initHeartbeats_3519_ = v_initHeartbeats_3504_;
v_maxHeartbeats_3520_ = v_maxHeartbeats_3505_;
v_quotContext_3521_ = v_quotContext_3506_;
v_currMacroScope_3522_ = v_currMacroScope_3507_;
v_cancelTk_x3f_3523_ = v_cancelTk_x3f_3508_;
v_inheritedTraceOptions_3524_ = v_inheritedTraceOptions_3509_;
v_currRecDepth_3525_ = v_currRecDepth_3495_;
v_ref_3526_ = v_ref_3496_;
v_suppressElabErrors_3527_ = v_suppressElabErrors_3497_;
v_isRecordingDeps_3528_ = v_isRecordingDeps_3498_;
v___y_3529_ = v_a_3490_;
goto v___jp_3512_;
}
else
{
v___y_3536_ = v___x_3511_;
v___y_3537_ = v___y_3561_;
v___y_3538_ = v___x_3562_;
goto v___jp_3535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3574_, lean_object* v_info_3575_, lean_object* v_name_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3574_, v_info_3575_, v_name_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec(v_a_3578_);
lean_dec_ref(v_a_3577_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3583_, lean_object* v_x_3584_, uint8_t v_isExporting_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3584_, v_isExporting_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_x_3593_, lean_object* v_isExporting_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
uint8_t v_isExporting_boxed_3600_; lean_object* v_res_3601_; 
v_isExporting_boxed_3600_ = lean_unbox(v_isExporting_3594_);
v_res_3601_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3592_, v_x_3593_, v_isExporting_boxed_3600_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
return v_res_3601_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3602_, lean_object* v_x_3603_, uint8_t v_when_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3603_, v_when_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3611_, lean_object* v_x_3612_, lean_object* v_when_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v_when_boxed_3619_; lean_object* v_res_3620_; 
v_when_boxed_3619_ = lean_unbox(v_when_3613_);
v_res_3620_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3611_, v_x_3612_, v_when_boxed_3619_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3621_, lean_object* v_info_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_){
_start:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v_env_3630_; lean_object* v_declName_3631_; lean_object* v_declNames_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3628_ = lean_box(0);
v___x_3629_ = lean_st_ref_get(v_a_3626_);
v_env_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc_ref(v_env_3630_);
lean_dec(v___x_3629_);
v_declName_3631_ = lean_ctor_get(v_info_3622_, 0);
v_declNames_3632_ = lean_ctor_get(v_info_3622_, 5);
v___x_3633_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3631_);
v___x_3634_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3630_, v_declName_3631_, v___x_3633_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_array_get(v___x_3628_, v_declNames_3632_, v___x_3635_);
lean_inc_n(v___x_3634_, 2);
lean_inc(v_declName_3621_);
v___x_3637_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3637_, 0, v_declName_3621_);
lean_closure_set(v___x_3637_, 1, v_info_3622_);
lean_closure_set(v___x_3637_, 2, v___x_3634_);
v___x_3638_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3638_, 0, lean_box(0));
lean_closure_set(v___x_3638_, 1, v_declName_3621_);
lean_closure_set(v___x_3638_, 2, v___x_3637_);
v___x_3639_ = l_Lean_Meta_realizeConst(v___x_3636_, v___x_3634_, v___x_3638_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3646_ == 0)
{
lean_object* v_unused_3647_; 
v_unused_3647_ = lean_ctor_get(v___x_3639_, 0);
lean_dec(v_unused_3647_);
v___x_3641_ = v___x_3639_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_dec(v___x_3639_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3634_);
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3634_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
else
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3655_; 
lean_dec(v___x_3634_);
v_a_3648_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3655_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3655_ == 0)
{
v___x_3650_ = v___x_3639_;
v_isShared_3651_ = v_isSharedCheck_3655_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3639_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3656_, lean_object* v_info_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3656_, v_info_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_env_3672_; lean_object* v___x_3673_; lean_object* v_toEnvExtension_3674_; lean_object* v_asyncMode_3675_; uint8_t v___x_3676_; lean_object* v___x_3677_; 
v___x_3670_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3671_ = lean_st_ref_get(v_a_3668_);
v_env_3672_ = lean_ctor_get(v___x_3671_, 0);
lean_inc_ref(v_env_3672_);
lean_dec(v___x_3671_);
v___x_3673_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3674_ = lean_ctor_get(v___x_3673_, 0);
v_asyncMode_3675_ = lean_ctor_get(v_toEnvExtension_3674_, 2);
v___x_3676_ = 0;
lean_inc(v_declName_3664_);
v___x_3677_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3670_, v___x_3673_, v_env_3672_, v_declName_3664_, v_asyncMode_3675_, v___x_3676_);
if (lean_obj_tag(v___x_3677_) == 1)
{
lean_object* v_val_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3702_; 
v_val_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_val_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3702_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; 
v___x_3682_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3664_, v_val_3678_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3693_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3693_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v_a_3683_);
v___x_3688_ = v___x_3680_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3690_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3688_);
v___x_3690_ = v___x_3685_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_del_object(v___x_3680_);
v_a_3694_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3682_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3682_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
else
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_dec(v___x_3677_);
lean_dec(v_declName_3664_);
v___x_3703_ = lean_box(0);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
return v___x_3704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3705_, v_a_3706_, v_a_3707_, v_a_3708_, v_a_3709_);
lean_dec(v_a_3709_);
lean_dec_ref(v_a_3708_);
lean_dec(v_a_3707_);
lean_dec_ref(v_a_3706_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v_env_3717_; lean_object* v___x_3718_; lean_object* v_toEnvExtension_3719_; lean_object* v_asyncMode_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
v___x_3715_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3716_ = lean_st_ref_get(v_a_3713_);
v_env_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc_ref(v_env_3717_);
lean_dec(v___x_3716_);
v___x_3718_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3719_ = lean_ctor_get(v___x_3718_, 0);
v_asyncMode_3720_ = lean_ctor_get(v_toEnvExtension_3719_, 2);
v___x_3721_ = 0;
v___x_3722_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3715_, v___x_3718_, v_env_3717_, v_declName_3712_, v_asyncMode_3720_, v___x_3721_);
if (lean_obj_tag(v___x_3722_) == 1)
{
lean_object* v_val_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3732_; 
v_val_3723_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3725_ = v___x_3722_;
v_isShared_3726_ = v_isSharedCheck_3732_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_val_3723_);
lean_dec(v___x_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3732_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v_recArgPos_3727_; lean_object* v___x_3729_; 
v_recArgPos_3727_ = lean_ctor_get(v_val_3723_, 4);
lean_inc(v_recArgPos_3727_);
lean_dec(v_val_3723_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v_recArgPos_3727_);
v___x_3729_ = v___x_3725_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_recArgPos_3727_);
v___x_3729_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_dec(v___x_3722_);
v___x_3733_ = lean_box(0);
v___x_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v_res_3738_; 
v_res_3738_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3735_, v_a_3736_);
lean_dec(v_a_3736_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v___x_3743_; 
lean_dec_ref(v_a_3740_);
v___x_3743_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3739_, v_a_3741_);
lean_dec(v_a_3741_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = lean_get_structural_rec_arg_pos(v_declName_3744_, v_a_3745_, v_a_3746_);
return v_res_3748_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3806_ = lean_unsigned_to_nat(2295916746u);
v___x_3807_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3808_ = l_Lean_Name_num___override(v___x_3807_, v___x_3806_);
return v___x_3808_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3811_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3812_ = l_Lean_Name_str___override(v___x_3811_, v___x_3810_);
return v___x_3812_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3814_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3815_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3816_ = l_Lean_Name_str___override(v___x_3815_, v___x_3814_);
return v___x_3816_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3817_ = lean_unsigned_to_nat(2u);
v___x_3818_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3819_ = l_Lean_Name_num___override(v___x_3818_, v___x_3817_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3822_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3821_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3823_; uint8_t v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec_ref_known(v___x_3822_, 1);
v___x_3823_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_3824_ = 0;
v___x_3825_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3826_ = l_Lean_registerTraceClass(v___x_3823_, v___x_3824_, v___x_3825_);
return v___x_3826_;
}
else
{
return v___x_3822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_3827_){
_start:
{
lean_object* v_res_3828_; 
v_res_3828_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_3828_;
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
