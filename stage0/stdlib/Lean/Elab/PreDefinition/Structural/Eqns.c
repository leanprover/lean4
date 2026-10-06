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
lean_inc(v___y_1095_);
v___x_1098_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1084_, v_data_1097_, v___y_1095_, v___y_1096_, v___y_1087_, v___y_1088_, v___y_1089_, v___y_1090_);
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
v___y_1095_ = v___y_1105_;
v___y_1096_ = v_a_1106_;
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
v___y_1095_ = v___y_1105_;
v___y_1096_ = v_a_1106_;
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
uint8_t v___x_1283_; 
v___x_1283_ = lean_nat_dec_le(v___x_1279_, v___x_1279_);
if (v___x_1283_ == 0)
{
if (v___x_1281_ == 0)
{
lean_object* v___x_1284_; 
lean_dec(v_declName_1272_);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1280_);
return v___x_1284_;
}
else
{
size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = ((size_t)0ULL);
v___x_1286_ = lean_usize_of_nat(v___x_1279_);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1272_, v_val_1270_, v___x_1285_, v___x_1286_, v___x_1280_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1287_;
}
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1279_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1272_, v_val_1270_, v___x_1288_, v___x_1289_, v___x_1280_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1290_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1306_, lean_object* v_mvarId_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v_toCold_1319_; lean_object* v_options_1320_; uint8_t v_hasTrace_1321_; 
v_toCold_1319_ = lean_ctor_get(v_a_1310_, 0);
v_options_1320_ = lean_ctor_get(v_toCold_1319_, 2);
v_hasTrace_1321_ = lean_ctor_get_uint8(v_options_1320_, sizeof(void*)*1);
if (v_hasTrace_1321_ == 0)
{
lean_object* v___x_1322_; 
lean_inc(v_mvarId_1307_);
v___x_1322_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1506_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1506_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1506_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
uint8_t v___x_1327_; 
v___x_1327_ = lean_unbox(v_a_1323_);
lean_dec(v_a_1323_);
if (v___x_1327_ == 0)
{
uint8_t v___x_1328_; lean_object* v___x_1329_; 
lean_del_object(v___x_1325_);
v___x_1328_ = 1;
lean_inc(v_mvarId_1307_);
v___x_1329_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1493_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1493_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1493_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
uint8_t v___x_1334_; 
v___x_1334_ = lean_unbox(v_a_1330_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
lean_del_object(v___x_1332_);
lean_inc(v_mvarId_1307_);
v___x_1335_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
if (lean_obj_tag(v_a_1336_) == 1)
{
lean_object* v_val_1337_; 
lean_dec(v_a_1330_);
lean_dec(v_mvarId_1307_);
v_val_1337_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v_a_1336_, 1);
v_mvarId_1307_ = v_val_1337_;
goto _start;
}
else
{
lean_object* v___x_1339_; 
lean_dec(v_a_1336_);
lean_inc(v_mvarId_1307_);
v___x_1339_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
if (lean_obj_tag(v_a_1340_) == 1)
{
lean_object* v_val_1341_; 
lean_dec(v_a_1330_);
lean_dec(v_mvarId_1307_);
v_val_1341_ = lean_ctor_get(v_a_1340_, 0);
lean_inc(v_val_1341_);
lean_dec_ref_known(v_a_1340_, 1);
v_mvarId_1307_ = v_val_1341_;
goto _start;
}
else
{
lean_object* v___x_1343_; 
lean_dec(v_a_1340_);
lean_inc(v_mvarId_1307_);
v___x_1343_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1307_, v___x_1328_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
if (lean_obj_tag(v_a_1344_) == 1)
{
lean_object* v_val_1345_; 
lean_dec(v_a_1330_);
lean_dec(v_mvarId_1307_);
v_val_1345_ = lean_ctor_get(v_a_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v_a_1344_, 1);
v_mvarId_1307_ = v_val_1345_;
goto _start;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; uint8_t v___x_1356_; uint8_t v___x_1357_; uint8_t v___x_1358_; uint8_t v___x_1359_; uint8_t v___x_1360_; uint8_t v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec(v_a_1344_);
v___x_1347_ = lean_unsigned_to_nat(100000u);
v___x_1348_ = lean_unsigned_to_nat(2u);
v___x_1349_ = 0;
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1351_, 0, v___x_1347_);
lean_ctor_set(v___x_1351_, 1, v___x_1348_);
lean_ctor_set(v___x_1351_, 2, v___x_1350_);
v___x_1352_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3, v___x_1352_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 1, v___x_1328_);
v___x_1353_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 2, v___x_1353_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 3, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 4, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 5, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 6, v___x_1349_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 7, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 8, v___x_1328_);
v___x_1354_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 9, v___x_1354_);
v___x_1355_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 10, v___x_1355_);
v___x_1356_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 11, v___x_1356_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 12, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 13, v___x_1328_);
v___x_1357_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 14, v___x_1357_);
v___x_1358_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 15, v___x_1358_);
v___x_1359_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 16, v___x_1359_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 17, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 18, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 19, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 20, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 21, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 22, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 23, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 24, v___x_1328_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 25, v___x_1328_);
v___x_1360_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 26, v___x_1360_);
v___x_1361_ = lean_unbox(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 27, v___x_1361_);
v___x_1362_ = lean_unbox(v_a_1330_);
lean_dec(v_a_1330_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3 + 28, v___x_1362_);
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1365_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1366_ = l_Lean_Options_empty;
v___x_1367_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1351_, v___x_1364_, v___x_1365_, v___x_1366_, v_a_1308_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_a_1368_);
lean_dec_ref_known(v___x_1367_, 1);
v___x_1369_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1307_);
v___x_1370_ = l_Lean_Meta_simpTargetStar(v_mvarId_1307_, v_a_1368_, v___x_1364_, v___x_1350_, v___x_1369_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1370_) == 0)
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1448_; 
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1373_ = v___x_1370_;
v_isShared_1374_ = v_isSharedCheck_1448_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1370_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1448_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_fst_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1446_; 
v_fst_1375_ = lean_ctor_get(v_a_1371_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_a_1371_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_a_1371_, 1);
lean_dec(v_unused_1447_);
v___x_1377_ = v_a_1371_;
v_isShared_1378_ = v_isSharedCheck_1446_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_fst_1375_);
lean_dec(v_a_1371_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1446_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
switch(lean_obj_tag(v_fst_1375_))
{
case 0:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_del_object(v___x_1377_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v___x_1379_ = lean_box(0);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1379_);
v___x_1381_ = v___x_1373_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
case 1:
{
lean_object* v___x_1383_; 
lean_del_object(v___x_1373_);
lean_inc(v_declName_1306_);
lean_inc(v_mvarId_1307_);
v___x_1383_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1307_, v_declName_1306_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
if (lean_obj_tag(v_a_1384_) == 1)
{
lean_object* v_val_1385_; 
lean_del_object(v___x_1377_);
lean_dec(v_mvarId_1307_);
v_val_1385_ = lean_ctor_get(v_a_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v_a_1384_, 1);
v_mvarId_1307_ = v_val_1385_;
goto _start;
}
else
{
lean_object* v___x_1387_; 
lean_dec(v_a_1384_);
lean_inc(v_mvarId_1307_);
v___x_1387_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1427_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1427_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1427_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1427_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1427_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
if (lean_obj_tag(v_a_1388_) == 1)
{
lean_object* v_val_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
lean_del_object(v___x_1377_);
lean_dec(v_mvarId_1307_);
v_val_1392_ = lean_ctor_get(v_a_1388_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v_a_1388_, 1);
v___x_1393_ = lean_array_get_size(v_val_1392_);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_nat_dec_lt(v___x_1363_, v___x_1393_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1397_; 
lean_dec(v_val_1392_);
lean_dec(v_declName_1306_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1394_);
v___x_1397_ = v___x_1390_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1394_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_le(v___x_1393_, v___x_1393_);
if (v___x_1399_ == 0)
{
if (v___x_1395_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v_val_1392_);
lean_dec(v_declName_1306_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1394_);
v___x_1401_ = v___x_1390_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1394_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
else
{
size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
lean_del_object(v___x_1390_);
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = lean_usize_of_nat(v___x_1393_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1306_, v_val_1392_, v___x_1403_, v___x_1404_, v___x_1394_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_val_1392_);
return v___x_1405_;
}
}
else
{
size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
lean_del_object(v___x_1390_);
v___x_1406_ = ((size_t)0ULL);
v___x_1407_ = lean_usize_of_nat(v___x_1393_);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1306_, v_val_1392_, v___x_1406_, v___x_1407_, v___x_1394_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_val_1392_);
return v___x_1408_;
}
}
}
else
{
lean_object* v___x_1409_; 
lean_del_object(v___x_1390_);
lean_dec(v_a_1388_);
lean_inc(v_mvarId_1307_);
v___x_1409_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1307_, v___x_1328_, v___x_1328_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
if (lean_obj_tag(v_a_1410_) == 1)
{
lean_object* v_val_1411_; lean_object* v___x_1412_; 
lean_del_object(v___x_1377_);
lean_dec(v_mvarId_1307_);
v_val_1411_ = lean_ctor_get(v_a_1410_, 0);
lean_inc(v_val_1411_);
lean_dec_ref_known(v_a_1410_, 1);
v___x_1412_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1306_, v_val_1411_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1412_;
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
lean_dec(v_a_1410_);
lean_dec(v_declName_1306_);
v___x_1413_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_mvarId_1307_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 7);
lean_ctor_set(v___x_1377_, 1, v___x_1414_);
lean_ctor_set(v___x_1377_, 0, v___x_1413_);
v___x_1416_ = v___x_1377_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1413_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1416_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1417_;
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1377_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1419_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1409_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1409_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_del_object(v___x_1377_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1428_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1387_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1387_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_del_object(v___x_1377_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1436_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1383_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1383_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1444_; 
lean_del_object(v___x_1377_);
lean_del_object(v___x_1373_);
lean_dec(v_mvarId_1307_);
v_mvarId_1444_ = lean_ctor_get(v_fst_1375_, 0);
lean_inc(v_mvarId_1444_);
lean_dec_ref_known(v_fst_1375_, 1);
v_mvarId_1307_ = v_mvarId_1444_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1449_ = lean_ctor_get(v___x_1370_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1370_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1370_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1370_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1457_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1367_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1367_);
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
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_a_1330_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1465_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1343_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1343_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec(v_a_1330_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1473_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1339_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1339_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_a_1330_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1481_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1335_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1335_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
lean_dec(v_a_1330_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v___x_1489_ = lean_box(0);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1489_);
v___x_1491_ = v___x_1332_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1494_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v___x_1329_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1329_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1504_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v___x_1502_ = lean_box(0);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1502_);
v___x_1504_ = v___x_1325_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1514_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1507_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1509_ = v___x_1322_;
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1322_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1514_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_a_1507_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1515_; lean_object* v___f_1516_; lean_object* v_cls_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v_a_1524_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v_a_1536_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v_a_1541_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v_a_1552_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v_a_1567_; lean_object* v___y_1570_; lean_object* v___y_1571_; lean_object* v_a_1572_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; 
v_inheritedTraceOptions_1515_ = lean_ctor_get(v_toCold_1319_, 11);
lean_inc(v_mvarId_1307_);
v___f_1516_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1516_, 0, v_mvarId_1307_);
v_cls_1517_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1518_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1519_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1520_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1515_, v_options_1320_, v___x_1519_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = l_Lean_trace_profiler;
v___x_1860_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1320_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v___f_1516_);
lean_inc(v_mvarId_1307_);
v___x_1861_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; uint8_t v___x_1863_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1863_ = lean_unbox(v_a_1862_);
lean_dec(v_a_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_inc(v_mvarId_1307_);
v___x_1864_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; uint8_t v___x_1866_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
v___x_1866_ = lean_unbox(v_a_1865_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_inc(v_mvarId_1307_);
v___x_1867_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
if (lean_obj_tag(v_a_1868_) == 1)
{
lean_dec(v_a_1865_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1869_; 
v_val_1869_ = lean_ctor_get(v_a_1868_, 0);
lean_inc(v_val_1869_);
lean_dec_ref_known(v_a_1868_, 1);
v_mvarId_1307_ = v_val_1869_;
goto _start;
}
else
{
lean_object* v_val_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_val_1871_ = lean_ctor_get(v_a_1868_, 0);
lean_inc(v_val_1871_);
lean_dec_ref_known(v_a_1868_, 1);
v___x_1872_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1873_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1872_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_dec_ref_known(v___x_1873_, 1);
v_mvarId_1307_ = v_val_1871_;
goto _start;
}
else
{
lean_dec(v_val_1871_);
lean_dec(v_declName_1306_);
return v___x_1873_;
}
}
}
else
{
lean_object* v___x_1875_; 
lean_dec(v_a_1868_);
lean_inc(v_mvarId_1307_);
v___x_1875_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
if (lean_obj_tag(v_a_1876_) == 1)
{
lean_dec(v_a_1865_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1877_; 
v_val_1877_ = lean_ctor_get(v_a_1876_, 0);
lean_inc(v_val_1877_);
lean_dec_ref_known(v_a_1876_, 1);
v_mvarId_1307_ = v_val_1877_;
goto _start;
}
else
{
lean_object* v_val_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_val_1879_ = lean_ctor_get(v_a_1876_, 0);
lean_inc(v_val_1879_);
lean_dec_ref_known(v_a_1876_, 1);
v___x_1880_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1881_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1880_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_dec_ref_known(v___x_1881_, 1);
v_mvarId_1307_ = v_val_1879_;
goto _start;
}
else
{
lean_dec(v_val_1879_);
lean_dec(v_declName_1306_);
return v___x_1881_;
}
}
}
else
{
lean_object* v___x_1883_; 
lean_dec(v_a_1876_);
lean_inc(v_mvarId_1307_);
v___x_1883_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1307_, v_hasTrace_1321_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
if (lean_obj_tag(v_a_1884_) == 1)
{
lean_dec(v_a_1865_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1885_; 
v_val_1885_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_val_1885_);
lean_dec_ref_known(v_a_1884_, 1);
v_mvarId_1307_ = v_val_1885_;
goto _start;
}
else
{
lean_object* v_val_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_val_1887_ = lean_ctor_get(v_a_1884_, 0);
lean_inc(v_val_1887_);
lean_dec_ref_known(v_a_1884_, 1);
v___x_1888_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1889_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1888_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_dec_ref_known(v___x_1889_, 1);
v_mvarId_1307_ = v_val_1887_;
goto _start;
}
else
{
lean_dec(v_val_1887_);
lean_dec(v_declName_1306_);
return v___x_1889_;
}
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; uint8_t v___x_1897_; uint8_t v___x_1898_; uint8_t v___x_1899_; uint8_t v___x_1900_; uint8_t v___x_1901_; uint8_t v___x_1902_; uint8_t v___x_1903_; uint8_t v___x_1904_; uint8_t v___x_1905_; uint8_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec(v_a_1884_);
v___x_1891_ = lean_unsigned_to_nat(100000u);
v___x_1892_ = lean_unsigned_to_nat(2u);
v___x_1893_ = 0;
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1895_, 0, v___x_1891_);
lean_ctor_set(v___x_1895_, 1, v___x_1892_);
lean_ctor_set(v___x_1895_, 2, v___x_1894_);
v___x_1896_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3, v___x_1896_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 1, v_hasTrace_1321_);
v___x_1897_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 2, v___x_1897_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 3, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 4, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 5, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 6, v___x_1893_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 7, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 8, v_hasTrace_1321_);
v___x_1898_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 9, v___x_1898_);
v___x_1899_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 10, v___x_1899_);
v___x_1900_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 11, v___x_1900_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 12, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 13, v_hasTrace_1321_);
v___x_1901_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 14, v___x_1901_);
v___x_1902_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 15, v___x_1902_);
v___x_1903_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 16, v___x_1903_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 17, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 18, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 19, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 20, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 21, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 22, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 23, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 24, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 25, v_hasTrace_1321_);
v___x_1904_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 26, v___x_1904_);
v___x_1905_ = lean_unbox(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 27, v___x_1905_);
v___x_1906_ = lean_unbox(v_a_1865_);
lean_dec(v_a_1865_);
lean_ctor_set_uint8(v___x_1895_, sizeof(void*)*3 + 28, v___x_1906_);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1909_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1910_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1911_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*2, v_hasTrace_1321_);
v___x_1912_ = l_Lean_Options_empty;
v___x_1913_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1895_, v___x_1908_, v___x_1911_, v___x_1912_, v_a_1308_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1307_);
v___x_1916_ = l_Lean_Meta_simpTargetStar(v_mvarId_1307_, v_a_1914_, v___x_1908_, v___x_1894_, v___x_1915_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_2015_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1919_ = v___x_1916_;
v_isShared_1920_ = v_isSharedCheck_2015_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1916_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_2015_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v_fst_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_2013_; 
v_fst_1921_ = lean_ctor_get(v_a_1917_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_a_1917_);
if (v_isSharedCheck_2013_ == 0)
{
lean_object* v_unused_2014_; 
v_unused_2014_ = lean_ctor_get(v_a_1917_, 1);
lean_dec(v_unused_2014_);
v___x_1923_ = v_a_1917_;
v_isShared_1924_ = v_isSharedCheck_2013_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_fst_1921_);
lean_dec(v_a_1917_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_2013_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
switch(lean_obj_tag(v_fst_1921_))
{
case 0:
{
lean_del_object(v___x_1923_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_box(0);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1925_);
v___x_1927_ = v___x_1919_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_del_object(v___x_1919_);
v___x_1929_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1930_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1929_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1930_;
}
}
case 1:
{
lean_object* v___x_1931_; 
lean_del_object(v___x_1919_);
lean_inc(v_declName_1306_);
lean_inc(v_mvarId_1307_);
v___x_1931_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1307_, v_declName_1306_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
if (lean_obj_tag(v_a_1932_) == 1)
{
lean_del_object(v___x_1923_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1933_; 
v_val_1933_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_val_1933_);
lean_dec_ref_known(v_a_1932_, 1);
v_mvarId_1307_ = v_val_1933_;
goto _start;
}
else
{
lean_object* v_val_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_val_1935_ = lean_ctor_get(v_a_1932_, 0);
lean_inc(v_val_1935_);
lean_dec_ref_known(v_a_1932_, 1);
v___x_1936_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1937_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1936_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_dec_ref_known(v___x_1937_, 1);
v_mvarId_1307_ = v_val_1935_;
goto _start;
}
else
{
lean_dec(v_val_1935_);
lean_dec(v_declName_1306_);
return v___x_1937_;
}
}
}
else
{
lean_object* v___x_1939_; 
lean_dec(v_a_1932_);
lean_inc(v_mvarId_1307_);
v___x_1939_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1990_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1942_ = v___x_1939_;
v_isShared_1943_ = v_isSharedCheck_1990_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1939_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1990_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
if (lean_obj_tag(v_a_1940_) == 1)
{
lean_object* v_val_1944_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; 
lean_del_object(v___x_1923_);
lean_dec(v_mvarId_1307_);
v_val_1944_ = lean_ctor_get(v_a_1940_, 0);
lean_inc(v_val_1944_);
lean_dec_ref_known(v_a_1940_, 1);
if (v___x_1520_ == 0)
{
v___y_1946_ = v_a_1308_;
v___y_1947_ = v_a_1309_;
v___y_1948_ = v_a_1310_;
v___y_1949_ = v_a_1311_;
goto v___jp_1945_;
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1967_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1966_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_dec_ref_known(v___x_1967_, 1);
v___y_1946_ = v_a_1308_;
v___y_1947_ = v_a_1309_;
v___y_1948_ = v_a_1310_;
v___y_1949_ = v_a_1311_;
goto v___jp_1945_;
}
else
{
lean_dec(v_val_1944_);
lean_del_object(v___x_1942_);
lean_dec(v_declName_1306_);
return v___x_1967_;
}
}
v___jp_1945_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = lean_array_get_size(v_val_1944_);
v___x_1951_ = lean_box(0);
v___x_1952_ = lean_nat_dec_lt(v___x_1907_, v___x_1950_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1954_; 
lean_dec(v_val_1944_);
lean_dec(v_declName_1306_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1951_);
v___x_1954_ = v___x_1942_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v___x_1951_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
else
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_nat_dec_le(v___x_1950_, v___x_1950_);
if (v___x_1956_ == 0)
{
if (v___x_1952_ == 0)
{
lean_object* v___x_1958_; 
lean_dec(v_val_1944_);
lean_dec(v_declName_1306_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1951_);
v___x_1958_ = v___x_1942_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1951_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
else
{
size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
lean_del_object(v___x_1942_);
v___x_1960_ = ((size_t)0ULL);
v___x_1961_ = lean_usize_of_nat(v___x_1950_);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1306_, v_val_1944_, v___x_1960_, v___x_1961_, v___x_1951_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v_val_1944_);
return v___x_1962_;
}
}
else
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
lean_del_object(v___x_1942_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1950_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1306_, v_val_1944_, v___x_1963_, v___x_1964_, v___x_1951_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v_val_1944_);
return v___x_1965_;
}
}
}
}
else
{
lean_object* v___x_1968_; 
lean_del_object(v___x_1942_);
lean_dec(v_a_1940_);
lean_inc(v_mvarId_1307_);
v___x_1968_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1307_, v_hasTrace_1321_, v_hasTrace_1321_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_a_1969_);
lean_dec_ref_known(v___x_1968_, 1);
if (lean_obj_tag(v_a_1969_) == 1)
{
lean_del_object(v___x_1923_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1970_; lean_object* v___x_1971_; 
v_val_1970_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_val_1970_);
lean_dec_ref_known(v_a_1969_, 1);
v___x_1971_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1306_, v_val_1970_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1971_;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_val_1972_ = lean_ctor_get(v_a_1969_, 0);
lean_inc(v_val_1972_);
lean_dec_ref_known(v_a_1969_, 1);
v___x_1973_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1974_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1973_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v___x_1975_; 
lean_dec_ref_known(v___x_1974_, 1);
v___x_1975_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1306_, v_val_1972_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1975_;
}
else
{
lean_dec(v_val_1972_);
lean_dec(v_declName_1306_);
return v___x_1974_;
}
}
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
lean_dec(v_a_1969_);
lean_dec(v_declName_1306_);
v___x_1976_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_mvarId_1307_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set_tag(v___x_1923_, 7);
lean_ctor_set(v___x_1923_, 1, v___x_1977_);
lean_ctor_set(v___x_1923_, 0, v___x_1976_);
v___x_1979_ = v___x_1923_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1979_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1980_;
}
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_del_object(v___x_1923_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1982_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1968_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1968_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_del_object(v___x_1923_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1991_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1939_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1939_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_del_object(v___x_1923_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1999_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1931_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1931_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
default: 
{
lean_del_object(v___x_1923_);
lean_del_object(v___x_1919_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_mvarId_2007_; 
v_mvarId_2007_ = lean_ctor_get(v_fst_1921_, 0);
lean_inc(v_mvarId_2007_);
lean_dec_ref_known(v_fst_1921_, 1);
v_mvarId_1307_ = v_mvarId_2007_;
goto _start;
}
else
{
lean_object* v_mvarId_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_mvarId_2009_ = lean_ctor_get(v_fst_1921_, 0);
lean_inc(v_mvarId_2009_);
lean_dec_ref_known(v_fst_1921_, 1);
v___x_2010_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2011_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_2010_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_dec_ref_known(v___x_2011_, 1);
v_mvarId_1307_ = v_mvarId_2009_;
goto _start;
}
else
{
lean_dec(v_mvarId_2009_);
lean_dec(v_declName_1306_);
return v___x_2011_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_2016_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_1916_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_1916_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_2024_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_1913_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_1913_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_1865_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_2032_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1883_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1883_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_1865_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_2040_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_1875_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_1875_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
}
else
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec(v_a_1865_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_2048_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v___x_1867_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_1867_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
else
{
lean_dec(v_a_1865_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
goto v___jp_1316_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2057_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_2056_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref_known(v___x_2057_, 1);
goto v___jp_1316_;
}
else
{
return v___x_2057_;
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_2058_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1864_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1864_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
else
{
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
goto v___jp_1313_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2067_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_2066_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_dec_ref_known(v___x_2067_, 1);
goto v___jp_1313_;
}
else
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_2068_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_1861_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_1861_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
else
{
goto v___jp_1580_;
}
}
else
{
goto v___jp_1580_;
}
v___jp_1521_:
{
lean_object* v___x_1525_; double v___x_1526_; double v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1525_ = lean_io_get_num_heartbeats();
v___x_1526_ = lean_float_of_nat(v___y_1522_);
v___x_1527_ = lean_float_of_nat(v___x_1525_);
v___x_1528_ = lean_box_float(v___x_1526_);
v___x_1529_ = lean_box_float(v___x_1527_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1531_, 0, v_a_1524_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1517_, v_hasTrace_1321_, v___x_1518_, v_options_1320_, v___x_1520_, v___y_1523_, v___f_1516_, v___x_1531_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1532_;
}
v___jp_1533_:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1536_);
v___y_1522_ = v___y_1534_;
v___y_1523_ = v___y_1535_;
v_a_1524_ = v___x_1537_;
goto v___jp_1521_;
}
v___jp_1538_:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1542_, 0, v_a_1541_);
v___y_1522_ = v___y_1539_;
v___y_1523_ = v___y_1540_;
v_a_1524_ = v___x_1542_;
goto v___jp_1521_;
}
v___jp_1543_:
{
if (lean_obj_tag(v___y_1546_) == 0)
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___y_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___y_1546_, 1);
v___y_1539_ = v___y_1544_;
v___y_1540_ = v___y_1545_;
v_a_1541_ = v_a_1547_;
goto v___jp_1538_;
}
else
{
lean_object* v_a_1548_; 
v_a_1548_ = lean_ctor_get(v___y_1546_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___y_1546_, 1);
v___y_1534_ = v___y_1544_;
v___y_1535_ = v___y_1545_;
v_a_1536_ = v_a_1548_;
goto v___jp_1533_;
}
}
v___jp_1549_:
{
lean_object* v___x_1553_; double v___x_1554_; double v___x_1555_; double v___x_1556_; double v___x_1557_; double v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1553_ = lean_io_mono_nanos_now();
v___x_1554_ = lean_float_of_nat(v___y_1550_);
v___x_1555_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1556_ = lean_float_div(v___x_1554_, v___x_1555_);
v___x_1557_ = lean_float_of_nat(v___x_1553_);
v___x_1558_ = lean_float_div(v___x_1557_, v___x_1555_);
v___x_1559_ = lean_box_float(v___x_1556_);
v___x_1560_ = lean_box_float(v___x_1558_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_a_1552_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1517_, v_hasTrace_1321_, v___x_1518_, v_options_1320_, v___x_1520_, v___y_1551_, v___f_1516_, v___x_1562_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1563_;
}
v___jp_1564_:
{
lean_object* v___x_1568_; 
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v_a_1567_);
v___y_1550_ = v___y_1565_;
v___y_1551_ = v___y_1566_;
v_a_1552_ = v___x_1568_;
goto v___jp_1549_;
}
v___jp_1569_:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_a_1572_);
v___y_1550_ = v___y_1570_;
v___y_1551_ = v___y_1571_;
v_a_1552_ = v___x_1573_;
goto v___jp_1549_;
}
v___jp_1574_:
{
if (lean_obj_tag(v___y_1577_) == 0)
{
lean_object* v_a_1578_; 
v_a_1578_ = lean_ctor_get(v___y_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___y_1577_, 1);
v___y_1565_ = v___y_1575_;
v___y_1566_ = v___y_1576_;
v_a_1567_ = v_a_1578_;
goto v___jp_1564_;
}
else
{
lean_object* v_a_1579_; 
v_a_1579_ = lean_ctor_get(v___y_1577_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___y_1577_, 1);
v___y_1570_ = v___y_1575_;
v___y_1571_ = v___y_1576_;
v_a_1572_ = v_a_1579_;
goto v___jp_1569_;
}
}
v___jp_1580_:
{
lean_object* v___x_1581_; 
v___x_1581_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1311_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; uint8_t v___x_1584_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1584_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1320_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1307_);
v___x_1586_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; uint8_t v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1588_ = lean_unbox(v_a_1587_);
lean_dec(v_a_1587_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; 
lean_inc(v_mvarId_1307_);
v___x_1589_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; uint8_t v___x_1591_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = lean_unbox(v_a_1590_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; 
lean_inc(v_mvarId_1307_);
v___x_1592_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
if (lean_obj_tag(v_a_1593_) == 1)
{
lean_dec(v_a_1590_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1594_; lean_object* v___x_1595_; 
v_val_1594_ = lean_ctor_get(v_a_1593_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_a_1593_, 1);
v___x_1595_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1594_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1595_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_val_1596_ = lean_ctor_get(v_a_1593_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v_a_1593_, 1);
v___x_1597_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1598_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1597_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v___x_1599_; 
lean_dec_ref_known(v___x_1598_, 1);
v___x_1599_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1596_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1599_;
goto v___jp_1574_;
}
else
{
lean_dec(v_val_1596_);
lean_dec(v_declName_1306_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1598_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v___x_1600_; 
lean_dec(v_a_1593_);
lean_inc(v_mvarId_1307_);
v___x_1600_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
if (lean_obj_tag(v_a_1601_) == 1)
{
lean_dec(v_a_1590_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1602_; lean_object* v___x_1603_; 
v_val_1602_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_val_1602_);
lean_dec_ref_known(v_a_1601_, 1);
v___x_1603_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1602_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1603_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_val_1604_ = lean_ctor_get(v_a_1601_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_a_1601_, 1);
v___x_1605_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1606_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1605_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; 
lean_dec_ref_known(v___x_1606_, 1);
v___x_1607_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1604_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1607_;
goto v___jp_1574_;
}
else
{
lean_dec(v_val_1604_);
lean_dec(v_declName_1306_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1606_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v___x_1608_; 
lean_dec(v_a_1601_);
lean_inc(v_mvarId_1307_);
v___x_1608_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1307_, v_hasTrace_1321_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v___x_1608_, 1);
if (lean_obj_tag(v_a_1609_) == 1)
{
lean_dec(v_a_1590_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1610_; lean_object* v___x_1611_; 
v_val_1610_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_a_1609_, 1);
v___x_1611_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1610_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1611_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_val_1612_ = lean_ctor_get(v_a_1609_, 0);
lean_inc(v_val_1612_);
lean_dec_ref_known(v_a_1609_, 1);
v___x_1613_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1614_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1613_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref_known(v___x_1614_, 1);
v___x_1615_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1612_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1615_;
goto v___jp_1574_;
}
else
{
lean_dec(v_val_1612_);
lean_dec(v_declName_1306_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1614_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; uint8_t v___x_1622_; uint8_t v___x_1623_; uint8_t v___x_1624_; uint8_t v___x_1625_; uint8_t v___x_1626_; uint8_t v___x_1627_; uint8_t v___x_1628_; uint8_t v___x_1629_; uint8_t v___x_1630_; uint8_t v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
lean_dec(v_a_1609_);
v___x_1616_ = lean_unsigned_to_nat(100000u);
v___x_1617_ = lean_unsigned_to_nat(2u);
v___x_1618_ = 0;
v___x_1619_ = lean_box(0);
v___x_1620_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1620_, 0, v___x_1616_);
lean_ctor_set(v___x_1620_, 1, v___x_1617_);
lean_ctor_set(v___x_1620_, 2, v___x_1619_);
v___x_1621_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3, v___x_1621_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 1, v_hasTrace_1321_);
v___x_1622_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 2, v___x_1622_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 3, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 4, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 5, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 6, v___x_1618_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 7, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 8, v_hasTrace_1321_);
v___x_1623_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 9, v___x_1623_);
v___x_1624_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 10, v___x_1624_);
v___x_1625_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 11, v___x_1625_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 12, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 13, v_hasTrace_1321_);
v___x_1626_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 14, v___x_1626_);
v___x_1627_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 15, v___x_1627_);
v___x_1628_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 16, v___x_1628_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 17, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 18, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 19, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 20, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 21, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 22, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 23, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 24, v_hasTrace_1321_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 25, v_hasTrace_1321_);
v___x_1629_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 26, v___x_1629_);
v___x_1630_ = lean_unbox(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 27, v___x_1630_);
v___x_1631_ = lean_unbox(v_a_1590_);
lean_dec(v_a_1590_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*3 + 28, v___x_1631_);
v___x_1632_ = lean_unsigned_to_nat(0u);
v___x_1633_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1634_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1636_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*2, v_hasTrace_1321_);
v___x_1637_ = l_Lean_Options_empty;
v___x_1638_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1620_, v___x_1633_, v___x_1636_, v___x_1637_, v_a_1308_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v___x_1640_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1307_);
v___x_1641_ = l_Lean_Meta_simpTargetStar(v_mvarId_1307_, v_a_1639_, v___x_1633_, v___x_1619_, v___x_1640_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_fst_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1697_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref_known(v___x_1641_, 1);
v_fst_1643_ = lean_ctor_get(v_a_1642_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_a_1642_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_a_1642_, 1);
lean_dec(v_unused_1698_);
v___x_1645_ = v_a_1642_;
v_isShared_1646_ = v_isSharedCheck_1697_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_fst_1643_);
lean_dec(v_a_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1697_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
switch(lean_obj_tag(v_fst_1643_))
{
case 0:
{
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_box(0);
v___y_1565_ = v___x_1585_;
v___y_1566_ = v_a_1582_;
v_a_1567_ = v___x_1647_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1649_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1648_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1649_;
goto v___jp_1574_;
}
}
case 1:
{
lean_object* v___x_1650_; 
lean_inc(v_declName_1306_);
lean_inc(v_mvarId_1307_);
v___x_1650_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1307_, v_declName_1306_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
if (lean_obj_tag(v_a_1651_) == 1)
{
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1652_; lean_object* v___x_1653_; 
v_val_1652_ = lean_ctor_get(v_a_1651_, 0);
lean_inc(v_val_1652_);
lean_dec_ref_known(v_a_1651_, 1);
v___x_1653_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1652_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1653_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_val_1654_ = lean_ctor_get(v_a_1651_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v_a_1651_, 1);
v___x_1655_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1656_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1655_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref_known(v___x_1656_, 1);
v___x_1657_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1654_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1657_;
goto v___jp_1574_;
}
else
{
lean_dec(v_val_1654_);
lean_dec(v_declName_1306_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1656_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v___x_1658_; 
lean_dec(v_a_1651_);
lean_inc(v_mvarId_1307_);
v___x_1658_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
if (lean_obj_tag(v_a_1659_) == 1)
{
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v_val_1660_ = lean_ctor_get(v_a_1659_, 0);
lean_inc(v_val_1660_);
lean_dec_ref_known(v_a_1659_, 1);
v___x_1661_ = lean_box(0);
v___x_1662_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1660_, v___x_1632_, v_declName_1306_, v___x_1661_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_val_1660_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1662_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v_val_1663_ = lean_ctor_get(v_a_1659_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v_a_1659_, 1);
v___x_1664_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1665_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1664_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1667_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_a_1666_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1667_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1663_, v___x_1632_, v_declName_1306_, v_a_1666_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_val_1663_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1667_;
goto v___jp_1574_;
}
else
{
lean_dec(v_val_1663_);
lean_dec(v_declName_1306_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1665_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v___x_1668_; 
lean_dec(v_a_1659_);
lean_inc(v_mvarId_1307_);
v___x_1668_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1307_, v_hasTrace_1321_, v_hasTrace_1321_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1687_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1687_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1687_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
if (lean_obj_tag(v_a_1669_) == 1)
{
lean_del_object(v___x_1671_);
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1673_; lean_object* v___x_1674_; 
v_val_1673_ = lean_ctor_get(v_a_1669_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v_a_1669_, 1);
v___x_1674_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1306_, v_val_1673_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1674_;
goto v___jp_1574_;
}
else
{
lean_object* v_val_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v_val_1675_ = lean_ctor_get(v_a_1669_, 0);
lean_inc(v_val_1675_);
lean_dec_ref_known(v_a_1669_, 1);
v___x_1676_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1677_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1676_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v___x_1678_; 
lean_dec_ref_known(v___x_1677_, 1);
v___x_1678_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1306_, v_val_1675_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1678_;
goto v___jp_1574_;
}
else
{
lean_dec(v_val_1675_);
lean_dec(v_declName_1306_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1677_;
goto v___jp_1574_;
}
}
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_dec(v_a_1669_);
lean_dec(v_declName_1306_);
v___x_1679_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 1);
lean_ctor_set(v___x_1671_, 0, v_mvarId_1307_);
v___x_1681_ = v___x_1671_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_mvarId_1307_);
v___x_1681_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set_tag(v___x_1645_, 7);
lean_ctor_set(v___x_1645_, 1, v___x_1681_);
lean_ctor_set(v___x_1645_, 0, v___x_1679_);
v___x_1683_ = v___x_1645_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1683_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1684_;
goto v___jp_1574_;
}
}
}
}
}
else
{
lean_object* v_a_1688_; 
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1688_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1668_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1688_;
goto v___jp_1569_;
}
}
}
else
{
lean_object* v_a_1689_; 
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1689_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1658_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1689_;
goto v___jp_1569_;
}
}
}
else
{
lean_object* v_a_1690_; 
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1690_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1650_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1690_;
goto v___jp_1569_;
}
}
default: 
{
lean_del_object(v___x_1645_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_mvarId_1691_; lean_object* v___x_1692_; 
v_mvarId_1691_ = lean_ctor_get(v_fst_1643_, 0);
lean_inc(v_mvarId_1691_);
lean_dec_ref_known(v_fst_1643_, 1);
v___x_1692_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_mvarId_1691_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1692_;
goto v___jp_1574_;
}
else
{
lean_object* v_mvarId_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_mvarId_1693_ = lean_ctor_get(v_fst_1643_, 0);
lean_inc(v_mvarId_1693_);
lean_dec_ref_known(v_fst_1643_, 1);
v___x_1694_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1695_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1694_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref_known(v___x_1695_, 1);
v___x_1696_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_mvarId_1693_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1696_;
goto v___jp_1574_;
}
else
{
lean_dec(v_mvarId_1693_);
lean_dec(v_declName_1306_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1695_;
goto v___jp_1574_;
}
}
}
}
}
}
else
{
lean_object* v_a_1699_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1699_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1641_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1699_;
goto v___jp_1569_;
}
}
else
{
lean_object* v_a_1700_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1700_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1638_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1700_;
goto v___jp_1569_;
}
}
}
else
{
lean_object* v_a_1701_; 
lean_dec(v_a_1590_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1701_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1608_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1701_;
goto v___jp_1569_;
}
}
}
else
{
lean_object* v_a_1702_; 
lean_dec(v_a_1590_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1702_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1600_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1702_;
goto v___jp_1569_;
}
}
}
else
{
lean_object* v_a_1703_; 
lean_dec(v_a_1590_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1703_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1592_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1703_;
goto v___jp_1569_;
}
}
else
{
lean_dec(v_a_1590_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_box(0);
v___x_1705_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1704_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1705_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1707_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1706_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1708_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1709_;
goto v___jp_1574_;
}
else
{
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1707_;
goto v___jp_1574_;
}
}
}
}
else
{
lean_object* v_a_1710_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1710_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1589_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1710_;
goto v___jp_1569_;
}
}
else
{
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1711_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1712_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1714_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1713_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1715_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1716_;
goto v___jp_1574_;
}
else
{
v___y_1575_ = v___x_1585_;
v___y_1576_ = v_a_1582_;
v___y_1577_ = v___x_1714_;
goto v___jp_1574_;
}
}
}
}
else
{
lean_object* v_a_1717_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1717_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1586_, 1);
v___y_1570_ = v___x_1585_;
v___y_1571_ = v_a_1582_;
v_a_1572_ = v_a_1717_;
goto v___jp_1569_;
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1307_);
v___x_1719_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; uint8_t v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = lean_unbox(v_a_1720_);
lean_dec(v_a_1720_);
if (v___x_1721_ == 0)
{
lean_object* v___x_1722_; 
lean_inc(v_mvarId_1307_);
v___x_1722_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; uint8_t v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = lean_unbox(v_a_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; 
lean_inc(v_mvarId_1307_);
v___x_1725_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
if (lean_obj_tag(v_a_1726_) == 1)
{
lean_dec(v_a_1723_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1727_; lean_object* v___x_1728_; 
v_val_1727_ = lean_ctor_get(v_a_1726_, 0);
lean_inc(v_val_1727_);
lean_dec_ref_known(v_a_1726_, 1);
v___x_1728_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1727_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1728_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v_val_1729_ = lean_ctor_get(v_a_1726_, 0);
lean_inc(v_val_1729_);
lean_dec_ref_known(v_a_1726_, 1);
v___x_1730_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1731_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1730_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v___x_1732_; 
lean_dec_ref_known(v___x_1731_, 1);
v___x_1732_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1729_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1732_;
goto v___jp_1543_;
}
else
{
lean_dec(v_val_1729_);
lean_dec(v_declName_1306_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1731_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v___x_1733_; 
lean_dec(v_a_1726_);
lean_inc(v_mvarId_1307_);
v___x_1733_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
if (lean_obj_tag(v_a_1734_) == 1)
{
lean_dec(v_a_1723_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1735_; lean_object* v___x_1736_; 
v_val_1735_ = lean_ctor_get(v_a_1734_, 0);
lean_inc(v_val_1735_);
lean_dec_ref_known(v_a_1734_, 1);
v___x_1736_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1735_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1736_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_val_1737_ = lean_ctor_get(v_a_1734_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v_a_1734_, 1);
v___x_1738_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1739_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1738_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref_known(v___x_1739_, 1);
v___x_1740_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1737_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1740_;
goto v___jp_1543_;
}
else
{
lean_dec(v_val_1737_);
lean_dec(v_declName_1306_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1739_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v___x_1741_; 
lean_dec(v_a_1734_);
lean_inc(v_mvarId_1307_);
v___x_1741_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1307_, v___x_1584_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 1);
if (lean_obj_tag(v_a_1742_) == 1)
{
lean_dec(v_a_1723_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1743_; lean_object* v___x_1744_; 
v_val_1743_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v_val_1743_);
lean_dec_ref_known(v_a_1742_, 1);
v___x_1744_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1743_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1744_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_val_1745_ = lean_ctor_get(v_a_1742_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v_a_1742_, 1);
v___x_1746_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1747_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1746_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v___x_1748_; 
lean_dec_ref_known(v___x_1747_, 1);
v___x_1748_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1745_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1748_;
goto v___jp_1543_;
}
else
{
lean_dec(v_val_1745_);
lean_dec(v_declName_1306_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1747_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; uint8_t v___x_1760_; uint8_t v___x_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v_a_1742_);
v___x_1749_ = lean_unsigned_to_nat(100000u);
v___x_1750_ = lean_unsigned_to_nat(2u);
v___x_1751_ = 0;
v___x_1752_ = lean_box(0);
v___x_1753_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1753_, 0, v___x_1749_);
lean_ctor_set(v___x_1753_, 1, v___x_1750_);
lean_ctor_set(v___x_1753_, 2, v___x_1752_);
v___x_1754_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3, v___x_1754_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 1, v___x_1584_);
v___x_1755_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 2, v___x_1755_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 3, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 4, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 5, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 6, v___x_1751_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 7, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 8, v___x_1584_);
v___x_1756_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 9, v___x_1756_);
v___x_1757_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 10, v___x_1757_);
v___x_1758_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 11, v___x_1758_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 12, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 13, v___x_1584_);
v___x_1759_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 14, v___x_1759_);
v___x_1760_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 15, v___x_1760_);
v___x_1761_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 16, v___x_1761_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 17, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 18, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 19, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 20, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 21, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 22, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 23, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 24, v___x_1584_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 25, v___x_1584_);
v___x_1762_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 26, v___x_1762_);
v___x_1763_ = lean_unbox(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 27, v___x_1763_);
v___x_1764_ = lean_unbox(v_a_1723_);
lean_dec(v_a_1723_);
lean_ctor_set_uint8(v___x_1753_, sizeof(void*)*3 + 28, v___x_1764_);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1767_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1768_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1769_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
lean_ctor_set_uint8(v___x_1769_, sizeof(void*)*2, v___x_1584_);
v___x_1770_ = l_Lean_Options_empty;
v___x_1771_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1753_, v___x_1766_, v___x_1769_, v___x_1770_, v_a_1308_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1773_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1307_);
v___x_1774_ = l_Lean_Meta_simpTargetStar(v_mvarId_1307_, v_a_1772_, v___x_1766_, v___x_1752_, v___x_1773_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v_fst_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1830_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v_fst_1776_ = lean_ctor_get(v_a_1775_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_a_1775_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v_a_1775_, 1);
lean_dec(v_unused_1831_);
v___x_1778_ = v_a_1775_;
v_isShared_1779_ = v_isSharedCheck_1830_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_fst_1776_);
lean_dec(v_a_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1830_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
switch(lean_obj_tag(v_fst_1776_))
{
case 0:
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_box(0);
v___y_1539_ = v___x_1718_;
v___y_1540_ = v_a_1582_;
v_a_1541_ = v___x_1780_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1782_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1781_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1782_;
goto v___jp_1543_;
}
}
case 1:
{
lean_object* v___x_1783_; 
lean_inc(v_declName_1306_);
lean_inc(v_mvarId_1307_);
v___x_1783_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1307_, v_declName_1306_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
if (lean_obj_tag(v_a_1784_) == 1)
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1785_; lean_object* v___x_1786_; 
v_val_1785_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_val_1785_);
lean_dec_ref_known(v_a_1784_, 1);
v___x_1786_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1785_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1786_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_val_1787_ = lean_ctor_get(v_a_1784_, 0);
lean_inc(v_val_1787_);
lean_dec_ref_known(v_a_1784_, 1);
v___x_1788_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1789_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1788_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v___x_1790_; 
lean_dec_ref_known(v___x_1789_, 1);
v___x_1790_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_val_1787_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1790_;
goto v___jp_1543_;
}
else
{
lean_dec(v_val_1787_);
lean_dec(v_declName_1306_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1789_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v___x_1791_; 
lean_dec(v_a_1784_);
lean_inc(v_mvarId_1307_);
v___x_1791_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
if (lean_obj_tag(v_a_1792_) == 1)
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_val_1793_ = lean_ctor_get(v_a_1792_, 0);
lean_inc(v_val_1793_);
lean_dec_ref_known(v_a_1792_, 1);
v___x_1794_ = lean_box(0);
v___x_1795_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1793_, v___x_1765_, v_declName_1306_, v___x_1794_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_val_1793_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1795_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_val_1796_ = lean_ctor_get(v_a_1792_, 0);
lean_inc(v_val_1796_);
lean_dec_ref_known(v_a_1792_, 1);
v___x_1797_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1798_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1797_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1800_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1796_, v___x_1765_, v_declName_1306_, v_a_1799_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec(v_val_1796_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1800_;
goto v___jp_1543_;
}
else
{
lean_dec(v_val_1796_);
lean_dec(v_declName_1306_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1798_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v___x_1801_; 
lean_dec(v_a_1792_);
lean_inc(v_mvarId_1307_);
v___x_1801_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1307_, v___x_1584_, v___x_1584_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1820_; 
v_a_1802_ = lean_ctor_get(v___x_1801_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1801_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1804_ = v___x_1801_;
v_isShared_1805_ = v_isSharedCheck_1820_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1801_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1820_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
if (lean_obj_tag(v_a_1802_) == 1)
{
lean_del_object(v___x_1804_);
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_val_1806_; lean_object* v___x_1807_; 
v_val_1806_ = lean_ctor_get(v_a_1802_, 0);
lean_inc(v_val_1806_);
lean_dec_ref_known(v_a_1802_, 1);
v___x_1807_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1306_, v_val_1806_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1807_;
goto v___jp_1543_;
}
else
{
lean_object* v_val_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v_val_1808_ = lean_ctor_get(v_a_1802_, 0);
lean_inc(v_val_1808_);
lean_dec_ref_known(v_a_1802_, 1);
v___x_1809_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1810_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1809_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref_known(v___x_1810_, 1);
v___x_1811_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1306_, v_val_1808_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1811_;
goto v___jp_1543_;
}
else
{
lean_dec(v_val_1808_);
lean_dec(v_declName_1306_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1810_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
lean_dec(v_a_1802_);
lean_dec(v_declName_1306_);
v___x_1812_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 1);
lean_ctor_set(v___x_1804_, 0, v_mvarId_1307_);
v___x_1814_ = v___x_1804_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_mvarId_1307_);
v___x_1814_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1816_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set_tag(v___x_1778_, 7);
lean_ctor_set(v___x_1778_, 1, v___x_1814_);
lean_ctor_set(v___x_1778_, 0, v___x_1812_);
v___x_1816_ = v___x_1778_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1816_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1817_;
goto v___jp_1543_;
}
}
}
}
}
else
{
lean_object* v_a_1821_; 
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1821_ = lean_ctor_get(v___x_1801_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1801_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1821_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1822_; 
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1822_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1822_);
lean_dec_ref_known(v___x_1791_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1822_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1823_; 
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1823_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1783_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1823_;
goto v___jp_1533_;
}
}
default: 
{
lean_del_object(v___x_1778_);
lean_dec(v_mvarId_1307_);
if (v___x_1520_ == 0)
{
lean_object* v_mvarId_1824_; lean_object* v___x_1825_; 
v_mvarId_1824_ = lean_ctor_get(v_fst_1776_, 0);
lean_inc(v_mvarId_1824_);
lean_dec_ref_known(v_fst_1776_, 1);
v___x_1825_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_mvarId_1824_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1825_;
goto v___jp_1543_;
}
else
{
lean_object* v_mvarId_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_mvarId_1826_ = lean_ctor_get(v_fst_1776_, 0);
lean_inc(v_mvarId_1826_);
lean_dec_ref_known(v_fst_1776_, 1);
v___x_1827_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1828_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1827_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v___x_1829_; 
lean_dec_ref_known(v___x_1828_, 1);
v___x_1829_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1306_, v_mvarId_1826_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1829_;
goto v___jp_1543_;
}
else
{
lean_dec(v_mvarId_1826_);
lean_dec(v_declName_1306_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1828_;
goto v___jp_1543_;
}
}
}
}
}
}
else
{
lean_object* v_a_1832_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1832_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1774_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1832_;
goto v___jp_1533_;
}
}
else
{
lean_object* v_a_1833_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1833_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1771_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1833_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1834_; 
lean_dec(v_a_1723_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1834_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1741_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1834_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1835_; 
lean_dec(v_a_1723_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1835_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1835_);
lean_dec_ref_known(v___x_1733_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1835_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1836_; 
lean_dec(v_a_1723_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1836_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1725_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1836_;
goto v___jp_1533_;
}
}
else
{
lean_dec(v_a_1723_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_box(0);
v___x_1838_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1837_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1838_;
goto v___jp_1543_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1840_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1839_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1841_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1842_;
goto v___jp_1543_;
}
else
{
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1840_;
goto v___jp_1543_;
}
}
}
}
else
{
lean_object* v_a_1843_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1843_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1722_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1843_;
goto v___jp_1533_;
}
}
else
{
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
if (v___x_1520_ == 0)
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_box(0);
v___x_1845_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1844_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1845_;
goto v___jp_1543_;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1847_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1517_, v___x_1846_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1848_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1849_;
goto v___jp_1543_;
}
else
{
v___y_1544_ = v___x_1718_;
v___y_1545_ = v_a_1582_;
v___y_1546_ = v___x_1847_;
goto v___jp_1543_;
}
}
}
}
else
{
lean_object* v_a_1850_; 
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1850_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1719_, 1);
v___y_1534_ = v___x_1718_;
v___y_1535_ = v_a_1582_;
v_a_1536_ = v_a_1850_;
goto v___jp_1533_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec_ref(v___f_1516_);
lean_dec(v_mvarId_1307_);
lean_dec(v_declName_1306_);
v_a_1851_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1581_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1581_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
v___jp_1316_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2076_, lean_object* v_as_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
if (lean_obj_tag(v_as_2077_) == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
lean_dec(v_declName_2076_);
v___x_2083_ = lean_box(0);
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
return v___x_2084_;
}
else
{
lean_object* v_head_2085_; lean_object* v_tail_2086_; lean_object* v___x_2087_; 
v_head_2085_ = lean_ctor_get(v_as_2077_, 0);
lean_inc(v_head_2085_);
v_tail_2086_ = lean_ctor_get(v_as_2077_, 1);
lean_inc(v_tail_2086_);
lean_dec_ref_known(v_as_2077_, 2);
lean_inc(v_declName_2076_);
v___x_2087_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2076_, v_head_2085_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_dec_ref_known(v___x_2087_, 1);
v_as_2077_ = v_tail_2086_;
goto _start;
}
else
{
lean_dec(v_tail_2086_);
lean_dec(v_declName_2076_);
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2089_, lean_object* v_as_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2089_, v_as_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2097_, lean_object* v_as_2098_, lean_object* v_i_2099_, lean_object* v_stop_2100_, lean_object* v_b_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
size_t v_i_boxed_2107_; size_t v_stop_boxed_2108_; lean_object* v_res_2109_; 
v_i_boxed_2107_ = lean_unbox_usize(v_i_2099_);
lean_dec(v_i_2099_);
v_stop_boxed_2108_ = lean_unbox_usize(v_stop_2100_);
lean_dec(v_stop_2100_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2097_, v_as_2098_, v_i_boxed_2107_, v_stop_boxed_2108_, v_b_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec_ref(v_as_2098_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2110_, lean_object* v___x_2111_, lean_object* v_declName_2112_, lean_object* v_____r_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2110_, v___x_2111_, v_declName_2112_, v_____r_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___x_2111_);
lean_dec_ref(v_val_2110_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2120_, lean_object* v_mvarId_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2120_, v_mvarId_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_00_u03b1_2128_, lean_object* v_x_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_2129_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_x_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_00_u03b1_2136_, v_x_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2144_, uint8_t v_skipRealize_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v_env_2149_; uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2148_ = lean_st_ref_get(v___y_2146_);
v_env_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc_ref(v_env_2149_);
lean_dec(v___x_2148_);
v___x_2150_ = l_Lean_Environment_contains(v_env_2149_, v_constName_2144_, v_skipRealize_2145_);
v___x_2151_ = lean_box(v___x_2150_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2153_, lean_object* v_skipRealize_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
uint8_t v_skipRealize_boxed_2157_; lean_object* v_res_2158_; 
v_skipRealize_boxed_2157_ = lean_unbox(v_skipRealize_2154_);
v_res_2158_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2153_, v_skipRealize_boxed_2157_, v___y_2155_);
lean_dec(v___y_2155_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2159_, uint8_t v_skipRealize_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2159_, v_skipRealize_2160_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2167_, lean_object* v_skipRealize_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
uint8_t v_skipRealize_boxed_2174_; lean_object* v_res_2175_; 
v_skipRealize_boxed_2174_ = lean_unbox(v_skipRealize_2168_);
v_res_2175_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2167_, v_skipRealize_boxed_2174_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2176_, lean_object* v___x_2177_, lean_object* v___x_2178_, lean_object* v_snd_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
lean_inc_ref(v_snd_2176_);
v___x_2185_ = l_Lean_Meta_mkCongrArg(v_snd_2176_, v___x_2177_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
v___x_2187_ = l_Lean_Expr_app___override(v_snd_2176_, v___x_2178_);
v___x_2188_ = l_Lean_MVarId_replaceTargetEq(v_snd_2179_, v___x_2187_, v_a_2186_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2188_;
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_snd_2179_);
lean_dec_ref(v___x_2178_);
lean_dec_ref(v_snd_2176_);
v_a_2189_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2185_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2185_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2197_, lean_object* v___x_2198_, lean_object* v___x_2199_, lean_object* v_snd_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2197_, v___x_2198_, v___x_2199_, v_snd_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2206_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2216_ = l_Lean_stringToMessageData(v___x_2215_);
return v___x_2216_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2219_ = l_Lean_stringToMessageData(v___x_2218_);
return v___x_2219_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2229_, lean_object* v___x_2230_, lean_object* v_cls_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
lean_inc(v_mvarId_2229_);
v___x_2237_ = l_Lean_MVarId_getType(v_mvarId_2229_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2239_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2238_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_fst_2241_; lean_object* v_snd_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2396_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v_fst_2241_ = lean_ctor_get(v_a_2240_, 0);
v_snd_2242_ = lean_ctor_get(v_a_2240_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2244_ = v_a_2240_;
v_isShared_2245_ = v_isSharedCheck_2396_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_snd_2242_);
lean_inc(v_fst_2241_);
lean_dec(v_a_2240_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2396_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v_dummy_2251_; lean_object* v_nargs_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; uint8_t v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2395_; 
v___x_2246_ = l_Lean_Expr_getAppFn(v_fst_2241_);
v___x_2247_ = l_Lean_Expr_constName_x21(v___x_2246_);
v___x_2248_ = l_Lean_Expr_constLevels_x21(v___x_2246_);
lean_dec_ref(v___x_2246_);
v___x_2249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2250_ = l_Lean_Name_str___override(v___x_2247_, v___x_2249_);
v_dummy_2251_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_2252_ = l_Lean_Expr_getAppNumArgs(v_fst_2241_);
lean_inc(v_nargs_2252_);
v___x_2253_ = lean_mk_array(v_nargs_2252_, v_dummy_2251_);
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_sub(v_nargs_2252_, v___x_2254_);
lean_dec(v_nargs_2252_);
v___x_2256_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2241_, v___x_2253_, v___x_2255_);
v___x_2370_ = 1;
lean_inc(v___x_2250_);
v___x_2371_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2250_, v___x_2370_, v___y_2235_);
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2395_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2395_;
goto v_resetjp_2373_;
}
v___jp_2257_:
{
lean_object* v___x_2266_; 
lean_inc(v___y_2265_);
lean_inc_ref(v___y_2264_);
lean_inc(v___y_2263_);
lean_inc_ref(v___y_2262_);
lean_inc_ref(v___y_2258_);
v___x_2266_ = lean_infer_type(v___y_2258_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2269_ = l_Lean_MVarId_define(v_mvarId_2229_, v___x_2268_, v_a_2267_, v___y_2258_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l_Lean_Meta_intro1Core(v_a_2270_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v_fst_2273_; lean_object* v_snd_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v_fst_2273_ = lean_ctor_get(v_a_2272_, 0);
lean_inc(v_fst_2273_);
v_snd_2274_ = lean_ctor_get(v_a_2272_, 1);
lean_inc_n(v_snd_2274_, 2);
lean_dec(v_a_2272_);
v___x_2275_ = l_Lean_Expr_appFn_x21(v___y_2260_);
lean_dec_ref(v___y_2260_);
v___x_2276_ = l_Lean_mkFVar(v_fst_2273_);
v___x_2277_ = l_Lean_Expr_app___override(v___x_2275_, v___x_2276_);
v___x_2278_ = l_Lean_mkAppN(v___y_2259_, v___x_2256_);
lean_dec_ref(v___x_2256_);
v___f_2279_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2279_, 0, v_snd_2242_);
lean_closure_set(v___f_2279_, 1, v___x_2278_);
lean_closure_set(v___f_2279_, 2, v___x_2277_);
lean_closure_set(v___f_2279_, 3, v_snd_2274_);
v___x_2280_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2274_, v___f_2279_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
return v___x_2280_;
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___x_2256_);
lean_dec(v_snd_2242_);
v_a_2281_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2271_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2271_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
else
{
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___x_2256_);
lean_dec(v_snd_2242_);
return v___x_2269_;
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___x_2256_);
lean_dec(v_snd_2242_);
lean_dec(v_mvarId_2229_);
v_a_2289_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2266_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2266_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
v___jp_2297_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_inc(v___x_2250_);
v___x_2302_ = l_Lean_mkConst(v___x_2250_, v___x_2248_);
lean_inc(v___y_2301_);
lean_inc_ref(v___y_2300_);
lean_inc(v___y_2299_);
lean_inc_ref(v___y_2298_);
lean_inc_ref(v___x_2302_);
v___x_2303_ = lean_infer_type(v___x_2302_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2305_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___x_2305_ = l_Lean_Meta_instantiateForall(v_a_2304_, v___x_2256_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v___x_2307_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2308_ = lean_unsigned_to_nat(3u);
v___x_2309_ = l_Lean_Expr_isAppOfArity(v_a_2306_, v___x_2307_, v___x_2308_);
if (v___x_2309_ == 0)
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
lean_dec(v_a_2306_);
lean_dec_ref(v___x_2302_);
lean_dec_ref(v___x_2256_);
lean_dec(v_snd_2242_);
lean_dec(v_cls_2231_);
v___x_2310_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2311_ = l_Lean_MessageData_ofName(v___x_2250_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 7);
lean_ctor_set(v___x_2244_, 1, v___x_2311_);
lean_ctor_set(v___x_2244_, 0, v___x_2310_);
v___x_2313_ = v___x_2244_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2310_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2314_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v_mvarId_2229_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2317_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v___x_2318_;
}
}
else
{
lean_object* v_toCold_2320_; lean_object* v_options_2321_; lean_object* v_inheritedTraceOptions_2322_; uint8_t v_hasTrace_2323_; lean_object* v___x_2324_; lean_object* v_nargs_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v___x_2250_);
v_toCold_2320_ = lean_ctor_get(v___y_2300_, 0);
v_options_2321_ = lean_ctor_get(v_toCold_2320_, 2);
v_inheritedTraceOptions_2322_ = lean_ctor_get(v_toCold_2320_, 11);
v_hasTrace_2323_ = lean_ctor_get_uint8(v_options_2321_, sizeof(void*)*1);
v___x_2324_ = l_Lean_Expr_appArg_x21(v_a_2306_);
lean_dec(v_a_2306_);
v_nargs_2325_ = l_Lean_Expr_getAppNumArgs(v___x_2324_);
lean_inc(v_nargs_2325_);
v___x_2326_ = lean_mk_array(v_nargs_2325_, v_dummy_2251_);
v___x_2327_ = lean_nat_sub(v_nargs_2325_, v___x_2254_);
lean_dec(v_nargs_2325_);
lean_inc_ref(v___x_2324_);
v___x_2328_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2324_, v___x_2326_, v___x_2327_);
v___x_2329_ = lean_array_get_size(v___x_2328_);
v___x_2330_ = lean_nat_sub(v___x_2329_, v___x_2254_);
v___x_2331_ = lean_array_get(v___x_2230_, v___x_2328_, v___x_2330_);
lean_dec(v___x_2330_);
lean_dec_ref(v___x_2328_);
if (v_hasTrace_2323_ == 0)
{
lean_del_object(v___x_2244_);
lean_dec(v_cls_2231_);
v___y_2258_ = v___x_2331_;
v___y_2259_ = v___x_2302_;
v___y_2260_ = v___x_2324_;
v___y_2261_ = v___x_2309_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
v___y_2265_ = v___y_2301_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; uint8_t v___x_2334_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2231_);
v___x_2333_ = l_Lean_Name_append(v___x_2332_, v_cls_2231_);
v___x_2334_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2322_, v_options_2321_, v___x_2333_);
lean_dec(v___x_2333_);
if (v___x_2334_ == 0)
{
lean_del_object(v___x_2244_);
lean_dec(v_cls_2231_);
v___y_2258_ = v___x_2331_;
v___y_2259_ = v___x_2302_;
v___y_2260_ = v___x_2324_;
v___y_2261_ = v___x_2309_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
v___y_2265_ = v___y_2301_;
goto v___jp_2257_;
}
else
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2335_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2336_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2331_);
v___x_2337_ = l_Lean_inlineExpr(v___x_2331_, v___x_2336_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set_tag(v___x_2244_, 7);
lean_ctor_set(v___x_2244_, 1, v___x_2337_);
lean_ctor_set(v___x_2244_, 0, v___x_2335_);
v___x_2339_ = v___x_2244_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v___x_2335_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v___x_2337_);
v___x_2339_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2340_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2339_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
lean_inc_ref(v___x_2324_);
v___x_2342_ = l_Lean_indentExpr(v___x_2324_);
v___x_2343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2341_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2231_, v___x_2343_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_dec_ref_known(v___x_2344_, 1);
v___y_2258_ = v___x_2331_;
v___y_2259_ = v___x_2302_;
v___y_2260_ = v___x_2324_;
v___y_2261_ = v___x_2309_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
v___y_2265_ = v___y_2301_;
goto v___jp_2257_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v___x_2331_);
lean_dec_ref(v___x_2324_);
lean_dec_ref(v___x_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v___x_2256_);
lean_dec(v_snd_2242_);
lean_dec(v_mvarId_2229_);
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2344_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
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
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v___x_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v___x_2256_);
lean_dec(v___x_2250_);
lean_del_object(v___x_2244_);
lean_dec(v_snd_2242_);
lean_dec(v_cls_2231_);
lean_dec(v_mvarId_2229_);
v_a_2354_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2305_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2305_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v___x_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v___x_2256_);
lean_dec(v___x_2250_);
lean_del_object(v___x_2244_);
lean_dec(v_snd_2242_);
lean_dec(v_cls_2231_);
lean_dec(v_mvarId_2229_);
v_a_2362_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2303_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2303_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
v_resetjp_2373_:
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_unbox(v_a_2372_);
lean_dec(v_a_2372_);
if (v___x_2376_ == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_dec_ref(v___x_2256_);
lean_dec(v___x_2248_);
lean_del_object(v___x_2244_);
lean_dec(v_snd_2242_);
lean_dec(v_cls_2231_);
v___x_2377_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2378_ = l_Lean_MessageData_ofName(v___x_2250_);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2379_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 1);
lean_ctor_set(v___x_2374_, 0, v_mvarId_2229_);
v___x_2383_ = v___x_2374_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_mvarId_2229_);
v___x_2383_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2381_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2384_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_del_object(v___x_2374_);
v___y_2298_ = v___y_2232_;
v___y_2299_ = v___y_2233_;
v___y_2300_ = v___y_2234_;
v___y_2301_ = v___y_2235_;
goto v___jp_2297_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v_cls_2231_);
lean_dec(v_mvarId_2229_);
v_a_2397_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2239_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2239_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v_cls_2231_);
lean_dec(v_mvarId_2229_);
v_a_2405_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2237_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2237_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2413_, lean_object* v___x_2414_, lean_object* v_cls_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2413_, v___x_2414_, v_cls_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec_ref(v___x_2414_);
return v_res_2421_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2424_ = l_Lean_stringToMessageData(v___x_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2425_, lean_object* v_x_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2432_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_mvarId_2425_);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2432_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2436_, lean_object* v_x_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2436_, v_x_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec_ref(v_x_2437_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2444_, lean_object* v_mvarId_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_toCold_2451_; lean_object* v_options_2452_; lean_object* v_inheritedTraceOptions_2453_; uint8_t v_hasTrace_2454_; lean_object* v___x_2455_; lean_object* v_cls_2456_; lean_object* v___f_2457_; 
v_toCold_2451_ = lean_ctor_get(v_a_2448_, 0);
v_options_2452_ = lean_ctor_get(v_toCold_2451_, 2);
v_inheritedTraceOptions_2453_ = lean_ctor_get(v_toCold_2451_, 11);
v_hasTrace_2454_ = lean_ctor_get_uint8(v_options_2452_, sizeof(void*)*1);
v___x_2455_ = l_Lean_instInhabitedExpr;
v_cls_2456_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2445_);
v___f_2457_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2457_, 0, v_mvarId_2445_);
lean_closure_set(v___f_2457_, 1, v___x_2455_);
lean_closure_set(v___f_2457_, 2, v_cls_2456_);
if (v_hasTrace_2454_ == 0)
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2445_, v___f_2457_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2460_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2444_, v_a_2459_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2460_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_declName_2444_);
v_a_2461_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2458_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2458_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
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
else
{
lean_object* v___f_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; lean_object* v___y_2474_; lean_object* v___y_2475_; lean_object* v_a_2476_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v_a_2491_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v_a_2496_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v_a_2508_; 
lean_inc(v_mvarId_2445_);
v___f_2469_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2469_, 0, v_mvarId_2445_);
v___x_2470_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2471_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2472_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2453_, v_options_2452_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2543_ = l_Lean_trace_profiler;
v___x_2544_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2452_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
lean_dec_ref(v___f_2469_);
v___x_2545_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2445_, v___f_2457_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2444_, v_a_2546_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2547_;
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_declName_2444_);
v_a_2548_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2545_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2545_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
else
{
goto v___jp_2510_;
}
}
else
{
goto v___jp_2510_;
}
v___jp_2473_:
{
lean_object* v___x_2477_; double v___x_2478_; double v___x_2479_; double v___x_2480_; double v___x_2481_; double v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2477_ = lean_io_mono_nanos_now();
v___x_2478_ = lean_float_of_nat(v___y_2474_);
v___x_2479_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2480_ = lean_float_div(v___x_2478_, v___x_2479_);
v___x_2481_ = lean_float_of_nat(v___x_2477_);
v___x_2482_ = lean_float_div(v___x_2481_, v___x_2479_);
v___x_2483_ = lean_box_float(v___x_2480_);
v___x_2484_ = lean_box_float(v___x_2482_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_a_2476_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2456_, v_hasTrace_2454_, v___x_2470_, v_options_2452_, v___x_2472_, v___y_2475_, v___f_2469_, v___x_2486_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2487_;
}
v___jp_2488_:
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_a_2491_);
v___y_2474_ = v___y_2489_;
v___y_2475_ = v___y_2490_;
v_a_2476_ = v___x_2492_;
goto v___jp_2473_;
}
v___jp_2493_:
{
lean_object* v___x_2497_; double v___x_2498_; double v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2497_ = lean_io_get_num_heartbeats();
v___x_2498_ = lean_float_of_nat(v___y_2494_);
v___x_2499_ = lean_float_of_nat(v___x_2497_);
v___x_2500_ = lean_box_float(v___x_2498_);
v___x_2501_ = lean_box_float(v___x_2499_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2496_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2456_, v_hasTrace_2454_, v___x_2470_, v_options_2452_, v___x_2472_, v___y_2495_, v___f_2469_, v___x_2503_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
return v___x_2504_;
}
v___jp_2505_:
{
lean_object* v___x_2509_; 
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_a_2508_);
v___y_2494_ = v___y_2506_;
v___y_2495_ = v___y_2507_;
v_a_2496_ = v___x_2509_;
goto v___jp_2493_;
}
v___jp_2510_:
{
lean_object* v___x_2511_; lean_object* v_a_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2511_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2449_);
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
v___x_2513_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2514_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2452_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = lean_io_mono_nanos_now();
v___x_2516_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2445_, v___f_2457_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2444_, v_a_2517_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
v_a_2519_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v___x_2518_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v___x_2518_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set_tag(v___x_2521_, 1);
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
v___y_2474_ = v___x_2515_;
v___y_2475_ = v_a_2512_;
v_a_2476_ = v___x_2524_;
goto v___jp_2473_;
}
}
}
else
{
lean_object* v_a_2527_; 
v_a_2527_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2518_, 1);
v___y_2489_ = v___x_2515_;
v___y_2490_ = v_a_2512_;
v_a_2491_ = v_a_2527_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2528_; 
lean_dec(v_declName_2444_);
v_a_2528_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2516_, 1);
v___y_2489_ = v___x_2515_;
v___y_2490_ = v_a_2512_;
v_a_2491_ = v_a_2528_;
goto v___jp_2488_;
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = lean_io_get_num_heartbeats();
v___x_2530_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2445_, v___f_2457_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2532_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2444_, v_a_2531_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2532_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2532_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set_tag(v___x_2535_, 1);
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
v___y_2494_ = v___x_2529_;
v___y_2495_ = v_a_2512_;
v_a_2496_ = v___x_2538_;
goto v___jp_2493_;
}
}
}
else
{
lean_object* v_a_2541_; 
v_a_2541_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2532_, 1);
v___y_2506_ = v___x_2529_;
v___y_2507_ = v_a_2512_;
v_a_2508_ = v_a_2541_;
goto v___jp_2505_;
}
}
else
{
lean_object* v_a_2542_; 
lean_dec(v_declName_2444_);
v_a_2542_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2530_, 1);
v___y_2506_ = v___x_2529_;
v___y_2507_ = v_a_2512_;
v_a_2508_ = v_a_2542_;
goto v___jp_2505_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2556_, lean_object* v_mvarId_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2556_, v_mvarId_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2564_, lean_object* v___y_2565_){
_start:
{
uint8_t v___x_2567_; 
v___x_2567_ = l_Lean_Expr_hasMVar(v_e_2564_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_e_2564_);
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; lean_object* v_mctx_2570_; lean_object* v___x_2571_; lean_object* v_fst_2572_; lean_object* v_snd_2573_; lean_object* v___x_2574_; lean_object* v_cache_2575_; lean_object* v_zetaDeltaFVarIds_2576_; lean_object* v_postponed_2577_; lean_object* v_diag_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2587_; 
v___x_2569_ = lean_st_ref_get(v___y_2565_);
v_mctx_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_ref(v_mctx_2570_);
lean_dec(v___x_2569_);
v___x_2571_ = l_Lean_instantiateMVarsCore(v_mctx_2570_, v_e_2564_);
v_fst_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_fst_2572_);
v_snd_2573_ = lean_ctor_get(v___x_2571_, 1);
lean_inc(v_snd_2573_);
lean_dec_ref(v___x_2571_);
v___x_2574_ = lean_st_ref_take(v___y_2565_);
v_cache_2575_ = lean_ctor_get(v___x_2574_, 1);
v_zetaDeltaFVarIds_2576_ = lean_ctor_get(v___x_2574_, 2);
v_postponed_2577_ = lean_ctor_get(v___x_2574_, 3);
v_diag_2578_ = lean_ctor_get(v___x_2574_, 4);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v___x_2574_, 0);
lean_dec(v_unused_2588_);
v___x_2580_ = v___x_2574_;
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_diag_2578_);
lean_inc(v_postponed_2577_);
lean_inc(v_zetaDeltaFVarIds_2576_);
lean_inc(v_cache_2575_);
lean_dec(v___x_2574_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 0, v_snd_2573_);
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_snd_2573_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_cache_2575_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_zetaDeltaFVarIds_2576_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_postponed_2577_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v_diag_2578_);
v___x_2583_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_st_ref_put(v___y_2565_, v___x_2583_);
v___x_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_fst_2572_);
return v___x_2585_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2589_, v___y_2590_);
lean_dec(v___y_2590_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2593_, v___y_2595_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2607_, uint8_t v_allowLevelAssignments_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2608_, v_k_2607_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
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
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
v_a_2623_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2614_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2614_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2631_, lean_object* v_allowLevelAssignments_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2638_; lean_object* v_res_2639_; 
v_allowLevelAssignments_boxed_2638_ = lean_unbox(v_allowLevelAssignments_2632_);
v_res_2639_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2631_, v_allowLevelAssignments_boxed_2638_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2640_, lean_object* v_k_2641_, uint8_t v_allowLevelAssignments_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2641_, v_allowLevelAssignments_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2649_, lean_object* v_k_2650_, lean_object* v_allowLevelAssignments_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2657_; lean_object* v_res_2658_; 
v_allowLevelAssignments_boxed_2657_ = lean_unbox(v_allowLevelAssignments_2651_);
v_res_2658_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2649_, v_k_2650_, v_allowLevelAssignments_boxed_2657_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2659_, lean_object* v_e_2660_){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = l_Lean_indentD(v_e_2660_);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2659_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2663_, lean_object* v___x_2664_, lean_object* v_declName_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2663_, v___x_2664_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = l_Lean_Expr_mvarId_x21(v_a_2672_);
v___x_2674_ = l_Lean_MVarId_intros(v___x_2673_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v_a_2675_; lean_object* v_snd_2676_; lean_object* v___x_2677_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v_snd_2676_ = lean_ctor_get(v_a_2675_, 1);
lean_inc_n(v_snd_2676_, 2);
lean_dec(v_a_2675_);
v___x_2677_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2676_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; uint8_t v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v___x_2679_ = lean_unbox(v_a_2678_);
lean_dec(v_a_2678_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2676_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2665_, v_a_2681_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref_known(v___x_2682_, 1);
v___x_2683_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2672_, v___y_2667_);
return v___x_2683_;
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_a_2672_);
v_a_2684_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2682_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2682_);
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
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
lean_dec(v_a_2672_);
lean_dec(v_declName_2665_);
v_a_2692_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2680_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2680_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v___x_2700_; 
lean_dec(v_snd_2676_);
lean_dec(v_declName_2665_);
v___x_2700_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2672_, v___y_2667_);
return v___x_2700_;
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_snd_2676_);
lean_dec(v_a_2672_);
lean_dec(v_declName_2665_);
v_a_2701_ = lean_ctor_get(v___x_2677_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2677_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2677_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_a_2672_);
lean_dec(v_declName_2665_);
v_a_2709_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2674_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2674_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_dec(v_declName_2665_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2717_, lean_object* v___x_2718_, lean_object* v_declName_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2717_, v___x_2718_, v_declName_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2725_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2728_ = l_Lean_stringToMessageData(v___x_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2729_, lean_object* v_x_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2737_ = l_Lean_indentExpr(v_type_2729_);
v___x_2738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2736_);
lean_ctor_set(v___x_2738_, 1, v___x_2737_);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2740_, lean_object* v_x_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2740_, v_x_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec_ref(v_x_2741_);
return v_res_2747_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2748_){
_start:
{
if (lean_obj_tag(v_e_2748_) == 0)
{
uint8_t v___x_2749_; 
v___x_2749_ = 2;
return v___x_2749_;
}
else
{
lean_object* v_a_2750_; uint8_t v___x_2751_; 
v_a_2750_ = lean_ctor_get(v_e_2748_, 0);
v___x_2751_ = l_Lean_Expr_hasSyntheticSorry(v_a_2750_);
if (v___x_2751_ == 0)
{
uint8_t v___x_2752_; 
v___x_2752_ = 0;
return v___x_2752_;
}
else
{
uint8_t v___x_2753_; 
v___x_2753_ = 1;
return v___x_2753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2754_){
_start:
{
uint8_t v_res_2755_; lean_object* v_r_2756_; 
v_res_2755_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2754_);
lean_dec_ref(v_e_2754_);
v_r_2756_ = lean_box(v_res_2755_);
return v_r_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2757_, uint8_t v_collapsed_2758_, lean_object* v_tag_2759_, lean_object* v_opts_2760_, uint8_t v_clsEnabled_2761_, lean_object* v_oldTraces_2762_, lean_object* v_msg_2763_, lean_object* v_resStartStop_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_fst_2770_; lean_object* v_snd_2771_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v_data_2775_; lean_object* v_fst_2786_; lean_object* v_snd_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; lean_object* v___y_2791_; lean_object* v_a_2792_; uint8_t v___y_2807_; double v___y_2839_; 
v_fst_2770_ = lean_ctor_get(v_resStartStop_2764_, 0);
lean_inc(v_fst_2770_);
v_snd_2771_ = lean_ctor_get(v_resStartStop_2764_, 1);
lean_inc(v_snd_2771_);
lean_dec_ref(v_resStartStop_2764_);
v_fst_2786_ = lean_ctor_get(v_snd_2771_, 0);
lean_inc(v_fst_2786_);
v_snd_2787_ = lean_ctor_get(v_snd_2771_, 1);
lean_inc(v_snd_2787_);
lean_dec(v_snd_2771_);
v___x_2788_ = l_Lean_trace_profiler;
v___x_2789_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2760_, v___x_2788_);
if (v___x_2789_ == 0)
{
v___y_2807_ = v___x_2789_;
goto v___jp_2806_;
}
else
{
lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2844_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2845_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2760_, v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; double v___x_2848_; double v___x_2849_; double v___x_2850_; 
v___x_2846_ = l_Lean_trace_profiler_threshold;
v___x_2847_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2760_, v___x_2846_);
v___x_2848_ = lean_float_of_nat(v___x_2847_);
v___x_2849_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_2850_ = lean_float_div(v___x_2848_, v___x_2849_);
v___y_2839_ = v___x_2850_;
goto v___jp_2838_;
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; double v___x_2853_; 
v___x_2851_ = l_Lean_trace_profiler_threshold;
v___x_2852_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2760_, v___x_2851_);
v___x_2853_ = lean_float_of_nat(v___x_2852_);
v___y_2839_ = v___x_2853_;
goto v___jp_2838_;
}
}
v___jp_2772_:
{
lean_object* v___x_2776_; 
lean_inc(v___y_2774_);
v___x_2776_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_2762_, v_data_2775_, v___y_2774_, v___y_2773_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v___x_2777_; 
lean_dec_ref_known(v___x_2776_, 1);
v___x_2777_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2770_);
return v___x_2777_;
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_fst_2770_);
v_a_2778_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2776_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2776_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
v___jp_2790_:
{
uint8_t v_result_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; double v___x_2796_; lean_object* v_data_2797_; 
v_result_2793_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2770_);
v___x_2794_ = lean_box(v_result_2793_);
v___x_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
v___x_2796_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2759_);
lean_inc_ref(v___x_2795_);
lean_inc(v_cls_2757_);
v_data_2797_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2797_, 0, v_cls_2757_);
lean_ctor_set(v_data_2797_, 1, v___x_2795_);
lean_ctor_set(v_data_2797_, 2, v_tag_2759_);
lean_ctor_set_float(v_data_2797_, sizeof(void*)*3, v___x_2796_);
lean_ctor_set_float(v_data_2797_, sizeof(void*)*3 + 8, v___x_2796_);
lean_ctor_set_uint8(v_data_2797_, sizeof(void*)*3 + 16, v_collapsed_2758_);
if (v___x_2789_ == 0)
{
lean_dec_ref_known(v___x_2795_, 1);
lean_dec(v_snd_2787_);
lean_dec(v_fst_2786_);
lean_dec_ref(v_tag_2759_);
lean_dec(v_cls_2757_);
v___y_2773_ = v_a_2792_;
v___y_2774_ = v___y_2791_;
v_data_2775_ = v_data_2797_;
goto v___jp_2772_;
}
else
{
lean_object* v_data_2798_; double v___x_2799_; double v___x_2800_; 
lean_dec_ref_known(v_data_2797_, 3);
v_data_2798_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2798_, 0, v_cls_2757_);
lean_ctor_set(v_data_2798_, 1, v___x_2795_);
lean_ctor_set(v_data_2798_, 2, v_tag_2759_);
v___x_2799_ = lean_unbox_float(v_fst_2786_);
lean_dec(v_fst_2786_);
lean_ctor_set_float(v_data_2798_, sizeof(void*)*3, v___x_2799_);
v___x_2800_ = lean_unbox_float(v_snd_2787_);
lean_dec(v_snd_2787_);
lean_ctor_set_float(v_data_2798_, sizeof(void*)*3 + 8, v___x_2800_);
lean_ctor_set_uint8(v_data_2798_, sizeof(void*)*3 + 16, v_collapsed_2758_);
v___y_2773_ = v_a_2792_;
v___y_2774_ = v___y_2791_;
v_data_2775_ = v_data_2798_;
goto v___jp_2772_;
}
}
v___jp_2801_:
{
lean_object* v_ref_2802_; lean_object* v___x_2803_; 
v_ref_2802_ = lean_ctor_get(v___y_2767_, 2);
lean_inc(v___y_2768_);
lean_inc_ref(v___y_2767_);
lean_inc(v___y_2766_);
lean_inc_ref(v___y_2765_);
lean_inc(v_fst_2770_);
v___x_2803_ = lean_apply_6(v_msg_2763_, v_fst_2770_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, lean_box(0));
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___y_2791_ = v_ref_2802_;
v_a_2792_ = v_a_2804_;
goto v___jp_2790_;
}
else
{
lean_object* v___x_2805_; 
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_2791_ = v_ref_2802_;
v_a_2792_ = v___x_2805_;
goto v___jp_2790_;
}
}
v___jp_2806_:
{
if (v_clsEnabled_2761_ == 0)
{
if (v___y_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v_traceState_2809_; lean_object* v_env_2810_; lean_object* v_nextMacroScope_2811_; lean_object* v_ngen_2812_; lean_object* v_auxDeclNGen_2813_; lean_object* v_cache_2814_; lean_object* v_recordedDeps_2815_; lean_object* v_messages_2816_; lean_object* v_infoState_2817_; lean_object* v_snapshotTasks_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2837_; 
lean_dec(v_snd_2787_);
lean_dec(v_fst_2786_);
lean_dec_ref(v_msg_2763_);
lean_dec_ref(v_tag_2759_);
lean_dec(v_cls_2757_);
v___x_2808_ = lean_st_ref_take(v___y_2768_);
v_traceState_2809_ = lean_ctor_get(v___x_2808_, 4);
v_env_2810_ = lean_ctor_get(v___x_2808_, 0);
v_nextMacroScope_2811_ = lean_ctor_get(v___x_2808_, 1);
v_ngen_2812_ = lean_ctor_get(v___x_2808_, 2);
v_auxDeclNGen_2813_ = lean_ctor_get(v___x_2808_, 3);
v_cache_2814_ = lean_ctor_get(v___x_2808_, 5);
v_recordedDeps_2815_ = lean_ctor_get(v___x_2808_, 6);
v_messages_2816_ = lean_ctor_get(v___x_2808_, 7);
v_infoState_2817_ = lean_ctor_get(v___x_2808_, 8);
v_snapshotTasks_2818_ = lean_ctor_get(v___x_2808_, 9);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2820_ = v___x_2808_;
v_isShared_2821_ = v_isSharedCheck_2837_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_snapshotTasks_2818_);
lean_inc(v_infoState_2817_);
lean_inc(v_messages_2816_);
lean_inc(v_recordedDeps_2815_);
lean_inc(v_cache_2814_);
lean_inc(v_traceState_2809_);
lean_inc(v_auxDeclNGen_2813_);
lean_inc(v_ngen_2812_);
lean_inc(v_nextMacroScope_2811_);
lean_inc(v_env_2810_);
lean_dec(v___x_2808_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2837_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
uint64_t v_tid_2822_; lean_object* v_traces_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2836_; 
v_tid_2822_ = lean_ctor_get_uint64(v_traceState_2809_, sizeof(void*)*1);
v_traces_2823_ = lean_ctor_get(v_traceState_2809_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_traceState_2809_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2825_ = v_traceState_2809_;
v_isShared_2826_ = v_isSharedCheck_2836_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_traces_2823_);
lean_dec(v_traceState_2809_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2836_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2827_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2762_, v_traces_2823_);
lean_dec_ref(v_traces_2823_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2827_);
v___x_2829_ = v___x_2825_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2827_);
lean_ctor_set_uint64(v_reuseFailAlloc_2835_, sizeof(void*)*1, v_tid_2822_);
v___x_2829_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2831_; 
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 4, v___x_2829_);
v___x_2831_ = v___x_2820_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_env_2810_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_nextMacroScope_2811_);
lean_ctor_set(v_reuseFailAlloc_2834_, 2, v_ngen_2812_);
lean_ctor_set(v_reuseFailAlloc_2834_, 3, v_auxDeclNGen_2813_);
lean_ctor_set(v_reuseFailAlloc_2834_, 4, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2834_, 5, v_cache_2814_);
lean_ctor_set(v_reuseFailAlloc_2834_, 6, v_recordedDeps_2815_);
lean_ctor_set(v_reuseFailAlloc_2834_, 7, v_messages_2816_);
lean_ctor_set(v_reuseFailAlloc_2834_, 8, v_infoState_2817_);
lean_ctor_set(v_reuseFailAlloc_2834_, 9, v_snapshotTasks_2818_);
v___x_2831_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_st_ref_put(v___y_2768_, v___x_2831_);
v___x_2833_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2770_);
return v___x_2833_;
}
}
}
}
}
else
{
goto v___jp_2801_;
}
}
else
{
goto v___jp_2801_;
}
}
v___jp_2838_:
{
double v___x_2840_; double v___x_2841_; double v___x_2842_; uint8_t v___x_2843_; 
v___x_2840_ = lean_unbox_float(v_snd_2787_);
v___x_2841_ = lean_unbox_float(v_fst_2786_);
v___x_2842_ = lean_float_sub(v___x_2840_, v___x_2841_);
v___x_2843_ = lean_float_decLt(v___y_2839_, v___x_2842_);
v___y_2807_ = v___x_2843_;
goto v___jp_2806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2854_, lean_object* v_collapsed_2855_, lean_object* v_tag_2856_, lean_object* v_opts_2857_, lean_object* v_clsEnabled_2858_, lean_object* v_oldTraces_2859_, lean_object* v_msg_2860_, lean_object* v_resStartStop_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v_collapsed_boxed_2867_; uint8_t v_clsEnabled_boxed_2868_; lean_object* v_res_2869_; 
v_collapsed_boxed_2867_ = lean_unbox(v_collapsed_2855_);
v_clsEnabled_boxed_2868_ = lean_unbox(v_clsEnabled_2858_);
v_res_2869_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2854_, v_collapsed_boxed_2867_, v_tag_2856_, v_opts_2857_, v_clsEnabled_boxed_2868_, v_oldTraces_2859_, v_msg_2860_, v_resStartStop_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec_ref(v_opts_2857_);
return v_res_2869_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2872_ = l_Lean_stringToMessageData(v___x_2871_);
return v___x_2872_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2875_ = l_Lean_stringToMessageData(v___x_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2876_, lean_object* v_type_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_toCold_2883_; lean_object* v_options_2884_; lean_object* v_inheritedTraceOptions_2885_; uint8_t v_hasTrace_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_toCold_2883_ = lean_ctor_get(v_a_2880_, 0);
v_options_2884_ = lean_ctor_get(v_toCold_2883_, 2);
v_inheritedTraceOptions_2885_ = lean_ctor_get(v_toCold_2883_, 11);
v_hasTrace_2886_ = lean_ctor_get_uint8(v_options_2884_, sizeof(void*)*1);
v___x_2887_ = 0;
lean_inc(v_declName_2876_);
v___x_2888_ = l_Lean_MessageData_ofConstName(v_declName_2876_, v___x_2887_);
v___x_2889_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
lean_ctor_set(v___x_2890_, 1, v___x_2888_);
v___x_2891_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___f_2893_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_2893_, 0, v___x_2892_);
v___x_2894_ = lean_box(0);
lean_inc_ref(v_type_2877_);
v___f_2895_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2895_, 0, v_type_2877_);
lean_closure_set(v___f_2895_, 1, v___x_2894_);
lean_closure_set(v___f_2895_, 2, v_declName_2876_);
v___x_2896_ = lean_box(v___x_2887_);
v___x_2897_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2897_, 0, lean_box(0));
lean_closure_set(v___x_2897_, 1, v___f_2895_);
lean_closure_set(v___x_2897_, 2, v___x_2896_);
if (v_hasTrace_2886_ == 0)
{
lean_object* v___x_2898_; 
lean_dec_ref(v_type_2877_);
v___x_2898_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_a_2907_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2898_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2898_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v___f_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v_a_2923_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v_a_2938_; 
v___f_2915_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2915_, 0, v_type_2877_);
v___x_2916_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_2917_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2918_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2919_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2885_, v_options_2884_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2988_; uint8_t v___x_2989_; 
v___x_2988_ = l_Lean_trace_profiler;
v___x_2989_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2884_, v___x_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; 
lean_dec_ref(v___f_2915_);
v___x_2990_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
v_a_2999_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2990_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2990_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
else
{
goto v___jp_2947_;
}
}
else
{
goto v___jp_2947_;
}
v___jp_2920_:
{
lean_object* v___x_2924_; double v___x_2925_; double v___x_2926_; double v___x_2927_; double v___x_2928_; double v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2924_ = lean_io_mono_nanos_now();
v___x_2925_ = lean_float_of_nat(v___y_2921_);
v___x_2926_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2927_ = lean_float_div(v___x_2925_, v___x_2926_);
v___x_2928_ = lean_float_of_nat(v___x_2924_);
v___x_2929_ = lean_float_div(v___x_2928_, v___x_2926_);
v___x_2930_ = lean_box_float(v___x_2927_);
v___x_2931_ = lean_box_float(v___x_2929_);
v___x_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2933_, 0, v_a_2923_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2916_, v_hasTrace_2886_, v___x_2917_, v_options_2884_, v___x_2919_, v___y_2922_, v___f_2915_, v___x_2933_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_2934_;
}
v___jp_2935_:
{
lean_object* v___x_2939_; double v___x_2940_; double v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2939_ = lean_io_get_num_heartbeats();
v___x_2940_ = lean_float_of_nat(v___y_2937_);
v___x_2941_ = lean_float_of_nat(v___x_2939_);
v___x_2942_ = lean_box_float(v___x_2940_);
v___x_2943_ = lean_box_float(v___x_2941_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_a_2938_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2916_, v_hasTrace_2886_, v___x_2917_, v_options_2884_, v___x_2919_, v___y_2936_, v___f_2915_, v___x_2945_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
return v___x_2946_;
}
v___jp_2947_:
{
lean_object* v___x_2948_; lean_object* v_a_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2948_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2881_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v___x_2950_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2951_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2884_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_io_mono_nanos_now();
v___x_2953_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
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
lean_ctor_set_tag(v___x_2956_, 1);
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
v___y_2921_ = v___x_2952_;
v___y_2922_ = v_a_2949_;
v_a_2923_ = v___x_2959_;
goto v___jp_2920_;
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
lean_ctor_set_tag(v___x_2964_, 0);
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
v___y_2921_ = v___x_2952_;
v___y_2922_ = v_a_2949_;
v_a_2923_ = v___x_2967_;
goto v___jp_2920_;
}
}
}
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_io_get_num_heartbeats();
v___x_2971_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2971_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set_tag(v___x_2974_, 1);
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
v___y_2936_ = v_a_2949_;
v___y_2937_ = v___x_2970_;
v_a_2938_ = v___x_2977_;
goto v___jp_2935_;
}
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
v_a_2980_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2971_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2971_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 0);
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
v___y_2936_ = v_a_2949_;
v___y_2937_ = v___x_2970_;
v_a_2938_ = v___x_2985_;
goto v___jp_2935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3007_, lean_object* v_type_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3007_, v_type_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
return v_res_3014_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_3015_, lean_object* v_n_3016_, lean_object* v_x_3017_){
_start:
{
uint8_t v___x_3018_; 
v___x_3018_ = l_Lean_Environment_hasExposedBody(v_env_3015_, v_n_3016_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_env_3019_, lean_object* v_n_3020_, lean_object* v_x_3021_){
_start:
{
uint8_t v_res_3022_; lean_object* v_r_3023_; 
v_res_3022_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(v_env_3019_, v_n_3020_, v_x_3021_);
lean_dec_ref(v_x_3021_);
v_r_3023_ = lean_box(v_res_3022_);
return v_r_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3024_, lean_object* v_x_3025_){
_start:
{
if (lean_obj_tag(v_x_3025_) == 0)
{
lean_object* v_k_3026_; lean_object* v_v_3027_; lean_object* v_l_3028_; lean_object* v_r_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_k_3026_ = lean_ctor_get(v_x_3025_, 1);
v_v_3027_ = lean_ctor_get(v_x_3025_, 2);
v_l_3028_ = lean_ctor_get(v_x_3025_, 3);
v_r_3029_ = lean_ctor_get(v_x_3025_, 4);
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3024_, v_l_3028_);
lean_inc(v_v_3027_);
lean_inc(v_k_3026_);
v___x_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3031_, 0, v_k_3026_);
lean_ctor_set(v___x_3031_, 1, v_v_3027_);
v___x_3032_ = lean_array_push(v___x_3030_, v___x_3031_);
v_init_3024_ = v___x_3032_;
v_x_3025_ = v_r_3029_;
goto _start;
}
else
{
return v_init_3024_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3034_, lean_object* v_x_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3034_, v_x_3035_);
lean_dec(v_x_3035_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(lean_object* v_env_3039_, lean_object* v_s_3040_){
_start:
{
lean_object* v___f_3041_; lean_object* v___x_3042_; lean_object* v_all_3043_; lean_object* v___x_3044_; lean_object* v_exported_3045_; lean_object* v___x_3046_; 
v___f_3041_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3041_, 0, v_env_3039_);
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v_all_3043_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_3042_, v_s_3040_);
v___x_3044_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3041_, v_s_3040_);
v_exported_3045_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v___x_3042_, v___x_3044_);
lean_dec(v___x_3044_);
lean_inc_ref(v_exported_3045_);
v___x_3046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3046_, 0, v_exported_3045_);
lean_ctor_set(v___x_3046_, 1, v_exported_3045_);
lean_ctor_set(v___x_3046_, 2, v_all_3043_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; lean_object* v___x_3063_; 
v___f_3059_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_));
v___x_3062_ = 1;
v___x_3063_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3060_, v___x_3061_, v___x_3062_, v___f_3059_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2____boxed(lean_object* v_a_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2_();
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0(lean_object* v_init_3066_, lean_object* v_t_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0_spec__0(v_init_3066_, v_t_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3069_, lean_object* v_t_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2576816323____hygCtx___hyg_2__spec__0(v_init_3069_, v_t_3070_);
lean_dec(v_t_3070_);
return v_res_3071_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3076_, lean_object* v_declNames_3077_, lean_object* v_recArgPos_3078_, lean_object* v_fixedParamPerms_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v_levelParams_3083_; lean_object* v_declName_3084_; lean_object* v_type_3085_; lean_object* v_value_3086_; lean_object* v___x_3087_; 
v_levelParams_3083_ = lean_ctor_get(v_preDef_3076_, 1);
lean_inc(v_levelParams_3083_);
v_declName_3084_ = lean_ctor_get(v_preDef_3076_, 3);
lean_inc_n(v_declName_3084_, 2);
v_type_3085_ = lean_ctor_get(v_preDef_3076_, 6);
lean_inc_ref(v_type_3085_);
v_value_3086_ = lean_ctor_get(v_preDef_3076_, 7);
lean_inc_ref(v_value_3086_);
lean_dec_ref(v_preDef_3076_);
v___x_3087_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3084_, v_a_3080_, v_a_3081_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3119_; 
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3120_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3119_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3119_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v_env_3092_; lean_object* v_nextMacroScope_3093_; lean_object* v_ngen_3094_; lean_object* v_auxDeclNGen_3095_; lean_object* v_traceState_3096_; lean_object* v_recordedDeps_3097_; lean_object* v_messages_3098_; lean_object* v_infoState_3099_; lean_object* v_snapshotTasks_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3117_; 
v___x_3091_ = lean_st_ref_take(v_a_3081_);
v_env_3092_ = lean_ctor_get(v___x_3091_, 0);
v_nextMacroScope_3093_ = lean_ctor_get(v___x_3091_, 1);
v_ngen_3094_ = lean_ctor_get(v___x_3091_, 2);
v_auxDeclNGen_3095_ = lean_ctor_get(v___x_3091_, 3);
v_traceState_3096_ = lean_ctor_get(v___x_3091_, 4);
v_recordedDeps_3097_ = lean_ctor_get(v___x_3091_, 6);
v_messages_3098_ = lean_ctor_get(v___x_3091_, 7);
v_infoState_3099_ = lean_ctor_get(v___x_3091_, 8);
v_snapshotTasks_3100_ = lean_ctor_get(v___x_3091_, 9);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3091_, 5);
lean_dec(v_unused_3118_);
v___x_3102_ = v___x_3091_;
v_isShared_3103_ = v_isSharedCheck_3117_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_snapshotTasks_3100_);
lean_inc(v_infoState_3099_);
lean_inc(v_messages_3098_);
lean_inc(v_recordedDeps_3097_);
lean_inc(v_traceState_3096_);
lean_inc(v_auxDeclNGen_3095_);
lean_inc(v_ngen_3094_);
lean_inc(v_nextMacroScope_3093_);
lean_inc(v_env_3092_);
lean_dec(v___x_3091_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3117_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3104_ = lean_box(0);
v___x_3105_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3084_);
v___x_3106_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3106_, 0, v_declName_3084_);
lean_ctor_set(v___x_3106_, 1, v_levelParams_3083_);
lean_ctor_set(v___x_3106_, 2, v_type_3085_);
lean_ctor_set(v___x_3106_, 3, v_value_3086_);
lean_ctor_set(v___x_3106_, 4, v_recArgPos_3078_);
lean_ctor_set(v___x_3106_, 5, v_declNames_3077_);
lean_ctor_set(v___x_3106_, 6, v_fixedParamPerms_3079_);
v___x_3107_ = 0;
v___x_3108_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3105_, v_env_3092_, v_declName_3084_, v___x_3106_, v___x_3107_);
v___x_3109_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 5, v___x_3109_);
lean_ctor_set(v___x_3102_, 0, v___x_3108_);
v___x_3111_ = v___x_3102_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3108_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_nextMacroScope_3093_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_ngen_3094_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_auxDeclNGen_3095_);
lean_ctor_set(v_reuseFailAlloc_3116_, 4, v_traceState_3096_);
lean_ctor_set(v_reuseFailAlloc_3116_, 5, v___x_3109_);
lean_ctor_set(v_reuseFailAlloc_3116_, 6, v_recordedDeps_3097_);
lean_ctor_set(v_reuseFailAlloc_3116_, 7, v_messages_3098_);
lean_ctor_set(v_reuseFailAlloc_3116_, 8, v_infoState_3099_);
lean_ctor_set(v_reuseFailAlloc_3116_, 9, v_snapshotTasks_3100_);
v___x_3111_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3112_ = lean_st_ref_put(v_a_3081_, v___x_3111_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3104_);
v___x_3114_ = v___x_3089_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3104_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
else
{
lean_dec_ref(v_value_3086_);
lean_dec_ref(v_type_3085_);
lean_dec(v_declName_3084_);
lean_dec(v_levelParams_3083_);
lean_dec_ref(v_fixedParamPerms_3079_);
lean_dec(v_recArgPos_3078_);
lean_dec_ref(v_declNames_3077_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3121_, lean_object* v_declNames_3122_, lean_object* v_recArgPos_3123_, lean_object* v_fixedParamPerms_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3121_, v_declNames_3122_, v_recArgPos_3123_, v_fixedParamPerms_3124_, v_a_3125_, v_a_3126_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(lean_object* v_e_3129_, lean_object* v_k_3130_, uint8_t v_cleanupAnnotations_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___f_3137_; uint8_t v___x_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___f_3137_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3137_, 0, v_k_3130_);
v___x_3138_ = 1;
v___x_3139_ = 0;
v___x_3140_ = lean_box(0);
v___x_3141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3129_, v___x_3138_, v___x_3139_, v___x_3138_, v___x_3139_, v___x_3140_, v___f_3137_, v_cleanupAnnotations_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_a_3150_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3141_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3141_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg___boxed(lean_object* v_e_3158_, lean_object* v_k_3159_, lean_object* v_cleanupAnnotations_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3166_; lean_object* v_res_3167_; 
v_cleanupAnnotations_boxed_3166_ = lean_unbox(v_cleanupAnnotations_3160_);
v_res_3167_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_e_3158_, v_k_3159_, v_cleanupAnnotations_boxed_3166_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_00_u03b1_3168_, lean_object* v_e_3169_, lean_object* v_k_3170_, uint8_t v_cleanupAnnotations_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_e_3169_, v_k_3170_, v_cleanupAnnotations_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_00_u03b1_3178_, lean_object* v_e_3179_, lean_object* v_k_3180_, lean_object* v_cleanupAnnotations_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3187_; lean_object* v_res_3188_; 
v_cleanupAnnotations_boxed_3187_ = lean_unbox(v_cleanupAnnotations_3181_);
v_res_3188_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_00_u03b1_3178_, v_e_3179_, v_k_3180_, v_cleanupAnnotations_boxed_3187_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3189_, uint8_t v_isExporting_3190_, lean_object* v___x_3191_, lean_object* v___y_3192_, lean_object* v___x_3193_, lean_object* v_a_x3f_3194_){
_start:
{
lean_object* v___x_3196_; lean_object* v_env_3197_; lean_object* v_nextMacroScope_3198_; lean_object* v_ngen_3199_; lean_object* v_auxDeclNGen_3200_; lean_object* v_traceState_3201_; lean_object* v_recordedDeps_3202_; lean_object* v_messages_3203_; lean_object* v_infoState_3204_; lean_object* v_snapshotTasks_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3230_; 
v___x_3196_ = lean_st_ref_take(v___y_3189_);
v_env_3197_ = lean_ctor_get(v___x_3196_, 0);
v_nextMacroScope_3198_ = lean_ctor_get(v___x_3196_, 1);
v_ngen_3199_ = lean_ctor_get(v___x_3196_, 2);
v_auxDeclNGen_3200_ = lean_ctor_get(v___x_3196_, 3);
v_traceState_3201_ = lean_ctor_get(v___x_3196_, 4);
v_recordedDeps_3202_ = lean_ctor_get(v___x_3196_, 6);
v_messages_3203_ = lean_ctor_get(v___x_3196_, 7);
v_infoState_3204_ = lean_ctor_get(v___x_3196_, 8);
v_snapshotTasks_3205_ = lean_ctor_get(v___x_3196_, 9);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v___x_3196_, 5);
lean_dec(v_unused_3231_);
v___x_3207_ = v___x_3196_;
v_isShared_3208_ = v_isSharedCheck_3230_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_snapshotTasks_3205_);
lean_inc(v_infoState_3204_);
lean_inc(v_messages_3203_);
lean_inc(v_recordedDeps_3202_);
lean_inc(v_traceState_3201_);
lean_inc(v_auxDeclNGen_3200_);
lean_inc(v_ngen_3199_);
lean_inc(v_nextMacroScope_3198_);
lean_inc(v_env_3197_);
lean_dec(v___x_3196_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3230_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3209_ = l_Lean_Environment_setExporting(v_env_3197_, v_isExporting_3190_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 5, v___x_3191_);
lean_ctor_set(v___x_3207_, 0, v___x_3209_);
v___x_3211_ = v___x_3207_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3209_);
lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_nextMacroScope_3198_);
lean_ctor_set(v_reuseFailAlloc_3229_, 2, v_ngen_3199_);
lean_ctor_set(v_reuseFailAlloc_3229_, 3, v_auxDeclNGen_3200_);
lean_ctor_set(v_reuseFailAlloc_3229_, 4, v_traceState_3201_);
lean_ctor_set(v_reuseFailAlloc_3229_, 5, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3229_, 6, v_recordedDeps_3202_);
lean_ctor_set(v_reuseFailAlloc_3229_, 7, v_messages_3203_);
lean_ctor_set(v_reuseFailAlloc_3229_, 8, v_infoState_3204_);
lean_ctor_set(v_reuseFailAlloc_3229_, 9, v_snapshotTasks_3205_);
v___x_3211_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v_mctx_3214_; lean_object* v_zetaDeltaFVarIds_3215_; lean_object* v_postponed_3216_; lean_object* v_diag_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3227_; 
v___x_3212_ = lean_st_ref_put(v___y_3189_, v___x_3211_);
v___x_3213_ = lean_st_ref_take(v___y_3192_);
v_mctx_3214_ = lean_ctor_get(v___x_3213_, 0);
v_zetaDeltaFVarIds_3215_ = lean_ctor_get(v___x_3213_, 2);
v_postponed_3216_ = lean_ctor_get(v___x_3213_, 3);
v_diag_3217_ = lean_ctor_get(v___x_3213_, 4);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3213_, 1);
lean_dec(v_unused_3228_);
v___x_3219_ = v___x_3213_;
v_isShared_3220_ = v_isSharedCheck_3227_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_diag_3217_);
lean_inc(v_postponed_3216_);
lean_inc(v_zetaDeltaFVarIds_3215_);
lean_inc(v_mctx_3214_);
lean_dec(v___x_3213_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3227_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3221_ = lean_box(0);
if (v_isShared_3220_ == 0)
{
lean_ctor_set(v___x_3219_, 1, v___x_3193_);
v___x_3223_ = v___x_3219_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_mctx_3214_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_zetaDeltaFVarIds_3215_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_postponed_3216_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_diag_3217_);
v___x_3223_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_st_ref_put(v___y_3192_, v___x_3223_);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3221_);
return v___x_3225_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3232_, lean_object* v_isExporting_3233_, lean_object* v___x_3234_, lean_object* v___y_3235_, lean_object* v___x_3236_, lean_object* v_a_x3f_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v_isExporting_boxed_3239_; lean_object* v_res_3240_; 
v_isExporting_boxed_3239_ = lean_unbox(v_isExporting_3233_);
v_res_3240_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3232_, v_isExporting_boxed_3239_, v___x_3234_, v___y_3235_, v___x_3236_, v_a_x3f_3237_);
lean_dec(v_a_x3f_3237_);
lean_dec(v___y_3235_);
lean_dec(v___y_3232_);
return v_res_3240_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
lean_ctor_set(v___x_3242_, 2, v___x_3241_);
lean_ctor_set(v___x_3242_, 3, v___x_3241_);
lean_ctor_set(v___x_3242_, 4, v___x_3241_);
lean_ctor_set(v___x_3242_, 5, v___x_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3243_, uint8_t v_isExporting_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
lean_object* v___x_3250_; lean_object* v_env_3251_; lean_object* v___x_3252_; uint8_t v_isModule_3253_; 
v___x_3250_ = lean_st_ref_get(v___y_3248_);
v_env_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc_ref(v_env_3251_);
lean_dec(v___x_3250_);
v___x_3252_ = l_Lean_Environment_header(v_env_3251_);
v_isModule_3253_ = lean_ctor_get_uint8(v___x_3252_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3252_);
if (v_isModule_3253_ == 0)
{
lean_object* v___x_3254_; 
lean_dec_ref(v_env_3251_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
v___x_3254_ = lean_apply_5(v_x_3243_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, lean_box(0));
return v___x_3254_;
}
else
{
uint8_t v_isExporting_3255_; 
v_isExporting_3255_ = lean_ctor_get_uint8(v_env_3251_, sizeof(void*)*13);
lean_dec_ref(v_env_3251_);
if (v_isExporting_3244_ == 0)
{
if (v_isExporting_3255_ == 0)
{
lean_object* v___x_3322_; 
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
v___x_3322_ = lean_apply_5(v_x_3243_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, lean_box(0));
return v___x_3322_;
}
else
{
goto v___jp_3256_;
}
}
else
{
if (v_isExporting_3255_ == 0)
{
goto v___jp_3256_;
}
else
{
lean_object* v___x_3323_; 
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
v___x_3323_ = lean_apply_5(v_x_3243_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, lean_box(0));
return v___x_3323_;
}
}
v___jp_3256_:
{
lean_object* v___x_3257_; lean_object* v_env_3258_; lean_object* v_nextMacroScope_3259_; lean_object* v_ngen_3260_; lean_object* v_auxDeclNGen_3261_; lean_object* v_traceState_3262_; lean_object* v_recordedDeps_3263_; lean_object* v_messages_3264_; lean_object* v_infoState_3265_; lean_object* v_snapshotTasks_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3320_; 
v___x_3257_ = lean_st_ref_take(v___y_3248_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
v_nextMacroScope_3259_ = lean_ctor_get(v___x_3257_, 1);
v_ngen_3260_ = lean_ctor_get(v___x_3257_, 2);
v_auxDeclNGen_3261_ = lean_ctor_get(v___x_3257_, 3);
v_traceState_3262_ = lean_ctor_get(v___x_3257_, 4);
v_recordedDeps_3263_ = lean_ctor_get(v___x_3257_, 6);
v_messages_3264_ = lean_ctor_get(v___x_3257_, 7);
v_infoState_3265_ = lean_ctor_get(v___x_3257_, 8);
v_snapshotTasks_3266_ = lean_ctor_get(v___x_3257_, 9);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; 
v_unused_3321_ = lean_ctor_get(v___x_3257_, 5);
lean_dec(v_unused_3321_);
v___x_3268_ = v___x_3257_;
v_isShared_3269_ = v_isSharedCheck_3320_;
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
v_isShared_3269_ = v_isSharedCheck_3320_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3270_ = l_Lean_Environment_setExporting(v_env_3258_, v_isExporting_3244_);
v___x_3271_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 5, v___x_3271_);
lean_ctor_set(v___x_3268_, 0, v___x_3270_);
v___x_3273_ = v___x_3268_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_nextMacroScope_3259_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_ngen_3260_);
lean_ctor_set(v_reuseFailAlloc_3319_, 3, v_auxDeclNGen_3261_);
lean_ctor_set(v_reuseFailAlloc_3319_, 4, v_traceState_3262_);
lean_ctor_set(v_reuseFailAlloc_3319_, 5, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3319_, 6, v_recordedDeps_3263_);
lean_ctor_set(v_reuseFailAlloc_3319_, 7, v_messages_3264_);
lean_ctor_set(v_reuseFailAlloc_3319_, 8, v_infoState_3265_);
lean_ctor_set(v_reuseFailAlloc_3319_, 9, v_snapshotTasks_3266_);
v___x_3273_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v_mctx_3276_; lean_object* v_zetaDeltaFVarIds_3277_; lean_object* v_postponed_3278_; lean_object* v_diag_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3317_; 
v___x_3274_ = lean_st_ref_put(v___y_3248_, v___x_3273_);
v___x_3275_ = lean_st_ref_take(v___y_3246_);
v_mctx_3276_ = lean_ctor_get(v___x_3275_, 0);
v_zetaDeltaFVarIds_3277_ = lean_ctor_get(v___x_3275_, 2);
v_postponed_3278_ = lean_ctor_get(v___x_3275_, 3);
v_diag_3279_ = lean_ctor_get(v___x_3275_, 4);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v___x_3275_, 1);
lean_dec(v_unused_3318_);
v___x_3281_ = v___x_3275_;
v_isShared_3282_ = v_isSharedCheck_3317_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_diag_3279_);
lean_inc(v_postponed_3278_);
lean_inc(v_zetaDeltaFVarIds_3277_);
lean_inc(v_mctx_3276_);
lean_dec(v___x_3275_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3317_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3283_; lean_object* v___x_3285_; 
v___x_3283_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3282_ == 0)
{
lean_ctor_set(v___x_3281_, 1, v___x_3283_);
v___x_3285_ = v___x_3281_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_mctx_3276_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3316_, 2, v_zetaDeltaFVarIds_3277_);
lean_ctor_set(v_reuseFailAlloc_3316_, 3, v_postponed_3278_);
lean_ctor_set(v_reuseFailAlloc_3316_, 4, v_diag_3279_);
v___x_3285_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; lean_object* v_r_3287_; 
v___x_3286_ = lean_st_ref_put(v___y_3246_, v___x_3285_);
lean_inc(v___y_3248_);
lean_inc_ref(v___y_3247_);
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
v_r_3287_ = lean_apply_5(v_x_3243_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, lean_box(0));
if (lean_obj_tag(v_r_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3304_; 
v_a_3288_ = lean_ctor_get(v_r_3287_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_r_3287_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3290_ = v_r_3287_;
v_isShared_3291_ = v_isSharedCheck_3304_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v_r_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3304_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
lean_inc(v_a_3288_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set_tag(v___x_3290_, 1);
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3301_; 
v___x_3294_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3248_, v_isExporting_3255_, v___x_3271_, v___y_3246_, v___x_3283_, v___x_3293_);
lean_dec_ref(v___x_3293_);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3301_ == 0)
{
lean_object* v_unused_3302_; 
v_unused_3302_ = lean_ctor_get(v___x_3294_, 0);
lean_dec(v_unused_3302_);
v___x_3296_ = v___x_3294_;
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
else
{
lean_dec(v___x_3294_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3301_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3299_; 
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 0, v_a_3288_);
v___x_3299_ = v___x_3296_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v_a_3288_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
v_a_3305_ = lean_ctor_get(v_r_3287_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v_r_3287_, 1);
v___x_3306_ = lean_box(0);
v___x_3307_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3248_, v_isExporting_3255_, v___x_3271_, v___y_3246_, v___x_3283_, v___x_3306_);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; 
v_unused_3315_ = lean_ctor_get(v___x_3307_, 0);
lean_dec(v_unused_3315_);
v___x_3309_ = v___x_3307_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_dec(v___x_3307_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 1);
lean_ctor_set(v___x_3309_, 0, v_a_3305_);
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3305_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3324_, lean_object* v_isExporting_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
uint8_t v_isExporting_boxed_3331_; lean_object* v_res_3332_; 
v_isExporting_boxed_3331_ = lean_unbox(v_isExporting_3325_);
v_res_3332_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3324_, v_isExporting_boxed_3331_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
return v_res_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3333_, uint8_t v_when_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
if (v_when_3334_ == 0)
{
lean_object* v___x_3340_; 
lean_inc(v___y_3338_);
lean_inc_ref(v___y_3337_);
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
v___x_3340_ = lean_apply_5(v_x_3333_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, lean_box(0));
return v___x_3340_;
}
else
{
uint8_t v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = 0;
v___x_3342_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3333_, v___x_3341_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3343_, lean_object* v_when_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v_when_boxed_3350_; lean_object* v_res_3351_; 
v_when_boxed_3350_ = lean_unbox(v_when_3344_);
v_res_3351_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3343_, v_when_boxed_3350_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
if (lean_obj_tag(v_a_3352_) == 0)
{
lean_object* v___x_3354_; 
v___x_3354_ = l_List_reverse___redArg(v_a_3353_);
return v___x_3354_;
}
else
{
lean_object* v_head_3355_; lean_object* v_tail_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3365_; 
v_head_3355_ = lean_ctor_get(v_a_3352_, 0);
v_tail_3356_ = lean_ctor_get(v_a_3352_, 1);
v_isSharedCheck_3365_ = !lean_is_exclusive(v_a_3352_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3358_ = v_a_3352_;
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_tail_3356_);
lean_inc(v_head_3355_);
lean_dec(v_a_3352_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3365_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3360_ = l_Lean_mkLevelParam(v_head_3355_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 1, v_a_3353_);
lean_ctor_set(v___x_3358_, 0, v___x_3360_);
v___x_3362_ = v___x_3358_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3360_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_a_3353_);
v___x_3362_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
v_a_3352_ = v_tail_3356_;
v_a_3353_ = v___x_3362_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3366_, lean_object* v_declName_3367_, lean_object* v_name_3368_, lean_object* v_xs_3369_, lean_object* v_body_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v___x_3376_; lean_object* v_us_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3376_ = lean_box(0);
lean_inc(v_levelParams_3366_);
v_us_3377_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3366_, v___x_3376_);
lean_inc(v_declName_3367_);
v___x_3378_ = l_Lean_mkConst(v_declName_3367_, v_us_3377_);
v___x_3379_ = l_Lean_mkAppN(v___x_3378_, v_xs_3369_);
v___x_3380_ = l_Lean_Meta_mkEq(v___x_3379_, v_body_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc_n(v_a_3381_, 2);
lean_dec_ref_known(v___x_3380_, 1);
v___x_3382_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3382_, 0, v_declName_3367_);
lean_closure_set(v___x_3382_, 1, v_a_3381_);
v___x_3383_ = 1;
v___x_3384_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3382_, v___x_3383_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v_a_3385_; uint8_t v___x_3386_; uint8_t v___x_3387_; lean_object* v___x_3388_; 
v_a_3385_ = lean_ctor_get(v___x_3384_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3384_, 1);
v___x_3386_ = 0;
v___x_3387_ = 1;
v___x_3388_ = l_Lean_Meta_mkForallFVars(v_xs_3369_, v_a_3381_, v___x_3386_, v___x_3383_, v___x_3383_, v___x_3387_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = l_Lean_Meta_letToHave(v_a_3389_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3392_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___x_3392_ = l_Lean_Meta_mkLambdaFVars(v_xs_3369_, v_a_3385_, v___x_3386_, v___x_3383_, v___x_3386_, v___x_3383_, v___x_3387_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
lean_inc_n(v_name_3368_, 2);
v___x_3394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3394_, 0, v_name_3368_);
lean_ctor_set(v___x_3394_, 1, v_levelParams_3366_);
lean_ctor_set(v___x_3394_, 2, v_a_3391_);
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v_name_3368_);
lean_ctor_set(v___x_3395_, 1, v___x_3376_);
v___x_3396_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v_a_3393_);
lean_ctor_set(v___x_3396_, 2, v___x_3395_);
v___x_3397_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
v___x_3398_ = l_Lean_addDecl(v___x_3397_, v___x_3386_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v___x_3399_; 
lean_dec_ref_known(v___x_3398_, 1);
v___x_3399_ = l_Lean_inferDefEqAttr(v_name_3368_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
return v___x_3399_;
}
else
{
lean_dec(v_name_3368_);
return v___x_3398_;
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_a_3391_);
lean_dec(v_name_3368_);
lean_dec(v_levelParams_3366_);
v_a_3400_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3392_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3392_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_dec(v_a_3385_);
lean_dec(v_name_3368_);
lean_dec(v_levelParams_3366_);
v_a_3408_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3390_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3390_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec(v_a_3385_);
lean_dec(v_name_3368_);
lean_dec(v_levelParams_3366_);
v_a_3416_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3388_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3388_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec(v_a_3381_);
lean_dec(v_name_3368_);
lean_dec(v_levelParams_3366_);
v_a_3424_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3384_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3384_);
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
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec(v_name_3368_);
lean_dec(v_declName_3367_);
lean_dec(v_levelParams_3366_);
v_a_3432_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3380_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3380_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3440_, lean_object* v_declName_3441_, lean_object* v_name_3442_, lean_object* v_xs_3443_, lean_object* v_body_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3440_, v_declName_3441_, v_name_3442_, v_xs_3443_, v_body_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec_ref(v_xs_3443_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(lean_object* v_o_3451_, lean_object* v_k_3452_, uint8_t v_v_3453_){
_start:
{
lean_object* v_map_3454_; uint8_t v_hasTrace_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3469_; 
v_map_3454_ = lean_ctor_get(v_o_3451_, 0);
v_hasTrace_3455_ = lean_ctor_get_uint8(v_o_3451_, sizeof(void*)*1);
v_isSharedCheck_3469_ = !lean_is_exclusive(v_o_3451_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3457_ = v_o_3451_;
v_isShared_3458_ = v_isSharedCheck_3469_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_map_3454_);
lean_dec(v_o_3451_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3469_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3459_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3459_, 0, v_v_3453_);
lean_inc(v_k_3452_);
v___x_3460_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3452_, v___x_3459_, v_map_3454_);
if (v_hasTrace_3455_ == 0)
{
lean_object* v___x_3461_; uint8_t v___x_3462_; lean_object* v___x_3464_; 
v___x_3461_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3462_ = l_Lean_Name_isPrefixOf(v___x_3461_, v_k_3452_);
lean_dec(v_k_3452_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3460_);
v___x_3464_ = v___x_3457_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v___x_3460_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_ctor_set_uint8(v___x_3464_, sizeof(void*)*1, v___x_3462_);
return v___x_3464_;
}
}
else
{
lean_object* v___x_3467_; 
lean_dec(v_k_3452_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3460_);
v___x_3467_ = v___x_3457_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3460_);
lean_ctor_set_uint8(v_reuseFailAlloc_3468_, sizeof(void*)*1, v_hasTrace_3455_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4___boxed(lean_object* v_o_3470_, lean_object* v_k_3471_, lean_object* v_v_3472_){
_start:
{
uint8_t v_v_boxed_3473_; lean_object* v_res_3474_; 
v_v_boxed_3473_ = lean_unbox(v_v_3472_);
v_res_3474_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(v_o_3470_, v_k_3471_, v_v_boxed_3473_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_opts_3475_, lean_object* v_opt_3476_, uint8_t v_val_3477_){
_start:
{
lean_object* v_name_3478_; lean_object* v___x_3479_; 
v_name_3478_ = lean_ctor_get(v_opt_3476_, 0);
lean_inc(v_name_3478_);
lean_dec_ref(v_opt_3476_);
v___x_3479_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3_spec__4(v_opts_3475_, v_name_3478_, v_val_3477_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_opts_3480_, lean_object* v_opt_3481_, lean_object* v_val_3482_){
_start:
{
uint8_t v_val_boxed_3483_; lean_object* v_res_3484_; 
v_val_boxed_3483_ = lean_unbox(v_val_3482_);
v_res_3484_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_opts_3480_, v_opt_3481_, v_val_boxed_3483_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3485_, lean_object* v_info_3486_, lean_object* v_name_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
lean_object* v_toCold_3493_; lean_object* v_levelParams_3494_; lean_object* v_value_3495_; lean_object* v_currRecDepth_3496_; lean_object* v_ref_3497_; uint8_t v_suppressElabErrors_3498_; uint8_t v_isRecordingDeps_3499_; lean_object* v_fileName_3500_; lean_object* v_fileMap_3501_; lean_object* v_options_3502_; lean_object* v_currNamespace_3503_; lean_object* v_openDecls_3504_; lean_object* v_initHeartbeats_3505_; lean_object* v_maxHeartbeats_3506_; lean_object* v_quotContext_3507_; lean_object* v_currMacroScope_3508_; lean_object* v_cancelTk_x3f_3509_; lean_object* v_inheritedTraceOptions_3510_; lean_object* v___f_3511_; uint8_t v___x_3512_; uint16_t v___y_3514_; lean_object* v___y_3515_; lean_object* v_fileName_3516_; lean_object* v_fileMap_3517_; lean_object* v_currNamespace_3518_; lean_object* v_openDecls_3519_; lean_object* v_initHeartbeats_3520_; lean_object* v_maxHeartbeats_3521_; lean_object* v_quotContext_3522_; lean_object* v_currMacroScope_3523_; lean_object* v_cancelTk_x3f_3524_; lean_object* v_inheritedTraceOptions_3525_; lean_object* v_currRecDepth_3526_; lean_object* v_ref_3527_; uint8_t v_suppressElabErrors_3528_; uint8_t v_isRecordingDeps_3529_; lean_object* v___y_3530_; uint8_t v___y_3537_; uint16_t v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3562_; 
v_toCold_3493_ = lean_ctor_get(v_a_3490_, 0);
v_levelParams_3494_ = lean_ctor_get(v_info_3486_, 1);
lean_inc(v_levelParams_3494_);
v_value_3495_ = lean_ctor_get(v_info_3486_, 3);
lean_inc_ref(v_value_3495_);
lean_dec_ref(v_info_3486_);
v_currRecDepth_3496_ = lean_ctor_get(v_a_3490_, 1);
v_ref_3497_ = lean_ctor_get(v_a_3490_, 2);
v_suppressElabErrors_3498_ = lean_ctor_get_uint8(v_a_3490_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3499_ = lean_ctor_get_uint8(v_a_3490_, sizeof(void*)*3 + 3);
v_fileName_3500_ = lean_ctor_get(v_toCold_3493_, 0);
v_fileMap_3501_ = lean_ctor_get(v_toCold_3493_, 1);
v_options_3502_ = lean_ctor_get(v_toCold_3493_, 2);
v_currNamespace_3503_ = lean_ctor_get(v_toCold_3493_, 4);
v_openDecls_3504_ = lean_ctor_get(v_toCold_3493_, 5);
v_initHeartbeats_3505_ = lean_ctor_get(v_toCold_3493_, 6);
v_maxHeartbeats_3506_ = lean_ctor_get(v_toCold_3493_, 7);
v_quotContext_3507_ = lean_ctor_get(v_toCold_3493_, 8);
v_currMacroScope_3508_ = lean_ctor_get(v_toCold_3493_, 9);
v_cancelTk_x3f_3509_ = lean_ctor_get(v_toCold_3493_, 10);
v_inheritedTraceOptions_3510_ = lean_ctor_get(v_toCold_3493_, 11);
v___f_3511_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3511_, 0, v_levelParams_3494_);
lean_closure_set(v___f_3511_, 1, v_declName_3485_);
lean_closure_set(v___f_3511_, 2, v_name_3487_);
v___x_3512_ = 0;
if (v_isRecordingDeps_3499_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3502_);
v___x_3573_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_options_3502_, v___x_3572_, v_isRecordingDeps_3499_);
v___y_3562_ = v___x_3573_;
goto v___jp_3561_;
}
else
{
lean_object* v___x_3574_; 
lean_inc_ref(v_options_3502_);
v___x_3574_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_3502_);
v___y_3562_ = v___x_3574_;
goto v___jp_3561_;
}
v___jp_3513_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3531_ = l_Lean_maxRecDepth;
v___x_3532_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___y_3515_, v___x_3531_);
v___x_3533_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3533_, 0, v_fileName_3516_);
lean_ctor_set(v___x_3533_, 1, v_fileMap_3517_);
lean_ctor_set(v___x_3533_, 2, v___y_3515_);
lean_ctor_set(v___x_3533_, 3, v___x_3532_);
lean_ctor_set(v___x_3533_, 4, v_currNamespace_3518_);
lean_ctor_set(v___x_3533_, 5, v_openDecls_3519_);
lean_ctor_set(v___x_3533_, 6, v_initHeartbeats_3520_);
lean_ctor_set(v___x_3533_, 7, v_maxHeartbeats_3521_);
lean_ctor_set(v___x_3533_, 8, v_quotContext_3522_);
lean_ctor_set(v___x_3533_, 9, v_currMacroScope_3523_);
lean_ctor_set(v___x_3533_, 10, v_cancelTk_x3f_3524_);
lean_ctor_set(v___x_3533_, 11, v_inheritedTraceOptions_3525_);
lean_inc(v_ref_3527_);
lean_inc(v_currRecDepth_3526_);
v___x_3534_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v_currRecDepth_3526_);
lean_ctor_set(v___x_3534_, 2, v_ref_3527_);
lean_ctor_set_uint16(v___x_3534_, sizeof(void*)*3, v___y_3514_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 2, v_suppressElabErrors_3528_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*3 + 3, v_isRecordingDeps_3529_);
v___x_3535_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___redArg(v_value_3495_, v___f_3511_, v___x_3512_, v_a_3488_, v_a_3489_, v___x_3534_, v___y_3530_);
lean_dec_ref_known(v___x_3534_, 3);
return v___x_3535_;
}
v___jp_3536_:
{
lean_object* v___x_3540_; lean_object* v_env_3541_; lean_object* v_nextMacroScope_3542_; lean_object* v_ngen_3543_; lean_object* v_auxDeclNGen_3544_; lean_object* v_traceState_3545_; lean_object* v_recordedDeps_3546_; lean_object* v_messages_3547_; lean_object* v_infoState_3548_; lean_object* v_snapshotTasks_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3559_; 
v___x_3540_ = lean_st_ref_take(v_a_3491_);
v_env_3541_ = lean_ctor_get(v___x_3540_, 0);
v_nextMacroScope_3542_ = lean_ctor_get(v___x_3540_, 1);
v_ngen_3543_ = lean_ctor_get(v___x_3540_, 2);
v_auxDeclNGen_3544_ = lean_ctor_get(v___x_3540_, 3);
v_traceState_3545_ = lean_ctor_get(v___x_3540_, 4);
v_recordedDeps_3546_ = lean_ctor_get(v___x_3540_, 6);
v_messages_3547_ = lean_ctor_get(v___x_3540_, 7);
v_infoState_3548_ = lean_ctor_get(v___x_3540_, 8);
v_snapshotTasks_3549_ = lean_ctor_get(v___x_3540_, 9);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3559_ == 0)
{
lean_object* v_unused_3560_; 
v_unused_3560_ = lean_ctor_get(v___x_3540_, 5);
lean_dec(v_unused_3560_);
v___x_3551_ = v___x_3540_;
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_snapshotTasks_3549_);
lean_inc(v_infoState_3548_);
lean_inc(v_messages_3547_);
lean_inc(v_recordedDeps_3546_);
lean_inc(v_traceState_3545_);
lean_inc(v_auxDeclNGen_3544_);
lean_inc(v_ngen_3543_);
lean_inc(v_nextMacroScope_3542_);
lean_inc(v_env_3541_);
lean_dec(v___x_3540_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3559_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3553_ = l_Lean_Kernel_enableDiag(v_env_3541_, v___y_3537_);
v___x_3554_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 5, v___x_3554_);
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3556_ = v___x_3551_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3553_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_nextMacroScope_3542_);
lean_ctor_set(v_reuseFailAlloc_3558_, 2, v_ngen_3543_);
lean_ctor_set(v_reuseFailAlloc_3558_, 3, v_auxDeclNGen_3544_);
lean_ctor_set(v_reuseFailAlloc_3558_, 4, v_traceState_3545_);
lean_ctor_set(v_reuseFailAlloc_3558_, 5, v___x_3554_);
lean_ctor_set(v_reuseFailAlloc_3558_, 6, v_recordedDeps_3546_);
lean_ctor_set(v_reuseFailAlloc_3558_, 7, v_messages_3547_);
lean_ctor_set(v_reuseFailAlloc_3558_, 8, v_infoState_3548_);
lean_ctor_set(v_reuseFailAlloc_3558_, 9, v_snapshotTasks_3549_);
v___x_3556_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_st_ref_put(v_a_3491_, v___x_3556_);
lean_inc_ref(v_inheritedTraceOptions_3510_);
lean_inc(v_cancelTk_x3f_3509_);
lean_inc(v_currMacroScope_3508_);
lean_inc(v_quotContext_3507_);
lean_inc(v_maxHeartbeats_3506_);
lean_inc(v_initHeartbeats_3505_);
lean_inc(v_openDecls_3504_);
lean_inc(v_currNamespace_3503_);
lean_inc_ref(v_fileMap_3501_);
lean_inc_ref(v_fileName_3500_);
v___y_3514_ = v___y_3538_;
v___y_3515_ = v___y_3539_;
v_fileName_3516_ = v_fileName_3500_;
v_fileMap_3517_ = v_fileMap_3501_;
v_currNamespace_3518_ = v_currNamespace_3503_;
v_openDecls_3519_ = v_openDecls_3504_;
v_initHeartbeats_3520_ = v_initHeartbeats_3505_;
v_maxHeartbeats_3521_ = v_maxHeartbeats_3506_;
v_quotContext_3522_ = v_quotContext_3507_;
v_currMacroScope_3523_ = v_currMacroScope_3508_;
v_cancelTk_x3f_3524_ = v_cancelTk_x3f_3509_;
v_inheritedTraceOptions_3525_ = v_inheritedTraceOptions_3510_;
v_currRecDepth_3526_ = v_currRecDepth_3496_;
v_ref_3527_ = v_ref_3497_;
v_suppressElabErrors_3528_ = v_suppressElabErrors_3498_;
v_isRecordingDeps_3529_ = v_isRecordingDeps_3499_;
v___y_3530_ = v_a_3491_;
goto v___jp_3513_;
}
}
}
v___jp_3561_:
{
uint16_t v___x_3563_; lean_object* v___x_3564_; lean_object* v_env_3565_; uint8_t v___x_3566_; uint16_t v___x_3567_; uint16_t v___x_3568_; uint16_t v___x_3569_; uint8_t v___x_3570_; 
v___x_3563_ = l_Lean_OptionFlags_ofOptions(v___y_3562_);
v___x_3564_ = lean_st_ref_get(v_a_3491_);
v_env_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc_ref(v_env_3565_);
lean_dec(v___x_3564_);
v___x_3566_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3565_);
lean_dec_ref(v_env_3565_);
v___x_3567_ = 512;
v___x_3568_ = lean_uint16_land(v___x_3563_, v___x_3567_);
v___x_3569_ = 0;
v___x_3570_ = lean_uint16_dec_eq(v___x_3568_, v___x_3569_);
if (v___x_3570_ == 0)
{
if (v___x_3566_ == 0)
{
uint8_t v___x_3571_; 
v___x_3571_ = 1;
v___y_3537_ = v___x_3571_;
v___y_3538_ = v___x_3563_;
v___y_3539_ = v___y_3562_;
goto v___jp_3536_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3510_);
lean_inc(v_cancelTk_x3f_3509_);
lean_inc(v_currMacroScope_3508_);
lean_inc(v_quotContext_3507_);
lean_inc(v_maxHeartbeats_3506_);
lean_inc(v_initHeartbeats_3505_);
lean_inc(v_openDecls_3504_);
lean_inc(v_currNamespace_3503_);
lean_inc_ref(v_fileMap_3501_);
lean_inc_ref(v_fileName_3500_);
v___y_3514_ = v___x_3563_;
v___y_3515_ = v___y_3562_;
v_fileName_3516_ = v_fileName_3500_;
v_fileMap_3517_ = v_fileMap_3501_;
v_currNamespace_3518_ = v_currNamespace_3503_;
v_openDecls_3519_ = v_openDecls_3504_;
v_initHeartbeats_3520_ = v_initHeartbeats_3505_;
v_maxHeartbeats_3521_ = v_maxHeartbeats_3506_;
v_quotContext_3522_ = v_quotContext_3507_;
v_currMacroScope_3523_ = v_currMacroScope_3508_;
v_cancelTk_x3f_3524_ = v_cancelTk_x3f_3509_;
v_inheritedTraceOptions_3525_ = v_inheritedTraceOptions_3510_;
v_currRecDepth_3526_ = v_currRecDepth_3496_;
v_ref_3527_ = v_ref_3497_;
v_suppressElabErrors_3528_ = v_suppressElabErrors_3498_;
v_isRecordingDeps_3529_ = v_isRecordingDeps_3499_;
v___y_3530_ = v_a_3491_;
goto v___jp_3513_;
}
}
else
{
if (v___x_3566_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3510_);
lean_inc(v_cancelTk_x3f_3509_);
lean_inc(v_currMacroScope_3508_);
lean_inc(v_quotContext_3507_);
lean_inc(v_maxHeartbeats_3506_);
lean_inc(v_initHeartbeats_3505_);
lean_inc(v_openDecls_3504_);
lean_inc(v_currNamespace_3503_);
lean_inc_ref(v_fileMap_3501_);
lean_inc_ref(v_fileName_3500_);
v___y_3514_ = v___x_3563_;
v___y_3515_ = v___y_3562_;
v_fileName_3516_ = v_fileName_3500_;
v_fileMap_3517_ = v_fileMap_3501_;
v_currNamespace_3518_ = v_currNamespace_3503_;
v_openDecls_3519_ = v_openDecls_3504_;
v_initHeartbeats_3520_ = v_initHeartbeats_3505_;
v_maxHeartbeats_3521_ = v_maxHeartbeats_3506_;
v_quotContext_3522_ = v_quotContext_3507_;
v_currMacroScope_3523_ = v_currMacroScope_3508_;
v_cancelTk_x3f_3524_ = v_cancelTk_x3f_3509_;
v_inheritedTraceOptions_3525_ = v_inheritedTraceOptions_3510_;
v_currRecDepth_3526_ = v_currRecDepth_3496_;
v_ref_3527_ = v_ref_3497_;
v_suppressElabErrors_3528_ = v_suppressElabErrors_3498_;
v_isRecordingDeps_3529_ = v_isRecordingDeps_3499_;
v___y_3530_ = v_a_3491_;
goto v___jp_3513_;
}
else
{
v___y_3537_ = v___x_3512_;
v___y_3538_ = v___x_3563_;
v___y_3539_ = v___y_3562_;
goto v___jp_3536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3575_, lean_object* v_info_3576_, lean_object* v_name_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3575_, v_info_3576_, v_name_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3584_, lean_object* v_x_3585_, uint8_t v_isExporting_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3585_, v_isExporting_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3593_, lean_object* v_x_3594_, lean_object* v_isExporting_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
uint8_t v_isExporting_boxed_3601_; lean_object* v_res_3602_; 
v_isExporting_boxed_3601_ = lean_unbox(v_isExporting_3595_);
v_res_3602_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3593_, v_x_3594_, v_isExporting_boxed_3601_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3603_, lean_object* v_x_3604_, uint8_t v_when_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3604_, v_when_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3612_, lean_object* v_x_3613_, lean_object* v_when_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
uint8_t v_when_boxed_3620_; lean_object* v_res_3621_; 
v_when_boxed_3620_ = lean_unbox(v_when_3614_);
v_res_3621_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3612_, v_x_3613_, v_when_boxed_3620_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3622_, lean_object* v_info_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v_env_3631_; lean_object* v_declName_3632_; lean_object* v_declNames_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3629_ = lean_box(0);
v___x_3630_ = lean_st_ref_get(v_a_3627_);
v_env_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc_ref(v_env_3631_);
lean_dec(v___x_3630_);
v_declName_3632_ = lean_ctor_get(v_info_3623_, 0);
v_declNames_3633_ = lean_ctor_get(v_info_3623_, 5);
v___x_3634_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3632_);
v___x_3635_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3631_, v_declName_3632_, v___x_3634_);
v___x_3636_ = lean_unsigned_to_nat(0u);
v___x_3637_ = lean_array_get(v___x_3629_, v_declNames_3633_, v___x_3636_);
lean_inc_n(v___x_3635_, 2);
lean_inc(v_declName_3622_);
v___x_3638_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3638_, 0, v_declName_3622_);
lean_closure_set(v___x_3638_, 1, v_info_3623_);
lean_closure_set(v___x_3638_, 2, v___x_3635_);
v___x_3639_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3639_, 0, lean_box(0));
lean_closure_set(v___x_3639_, 1, v_declName_3622_);
lean_closure_set(v___x_3639_, 2, v___x_3638_);
v___x_3640_ = l_Lean_Meta_realizeConst(v___x_3637_, v___x_3635_, v___x_3639_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3647_ == 0)
{
lean_object* v_unused_3648_; 
v_unused_3648_ = lean_ctor_get(v___x_3640_, 0);
lean_dec(v_unused_3648_);
v___x_3642_ = v___x_3640_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_dec(v___x_3640_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3635_);
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3635_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec(v___x_3635_);
v_a_3649_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3640_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3640_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3657_, lean_object* v_info_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3657_, v_info_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v_env_3673_; lean_object* v___x_3674_; lean_object* v_toEnvExtension_3675_; lean_object* v_asyncMode_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; 
v___x_3671_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3672_ = lean_st_ref_get(v_a_3669_);
v_env_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc_ref(v_env_3673_);
lean_dec(v___x_3672_);
v___x_3674_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3675_ = lean_ctor_get(v___x_3674_, 0);
v_asyncMode_3676_ = lean_ctor_get(v_toEnvExtension_3675_, 2);
v___x_3677_ = 0;
lean_inc(v_declName_3665_);
v___x_3678_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3671_, v___x_3674_, v_env_3673_, v_declName_3665_, v_asyncMode_3676_, v___x_3677_);
if (lean_obj_tag(v___x_3678_) == 1)
{
lean_object* v_val_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3703_; 
v_val_3679_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3681_ = v___x_3678_;
v_isShared_3682_ = v_isSharedCheck_3703_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_val_3679_);
lean_dec(v___x_3678_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3703_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3683_; 
v___x_3683_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3665_, v_val_3679_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3694_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3686_ = v___x_3683_;
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3694_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3689_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v_a_3684_);
v___x_3689_ = v___x_3681_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3684_);
v___x_3689_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3691_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3689_);
v___x_3691_ = v___x_3686_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3689_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_del_object(v___x_3681_);
v_a_3695_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3683_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3683_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
else
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_dec(v___x_3678_);
lean_dec(v_declName_3665_);
v___x_3704_ = lean_box(0);
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v_res_3712_; 
v_res_3712_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3706_, v_a_3707_, v_a_3708_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
return v_res_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v_env_3718_; lean_object* v___x_3719_; lean_object* v_toEnvExtension_3720_; lean_object* v_asyncMode_3721_; uint8_t v___x_3722_; lean_object* v___x_3723_; 
v___x_3716_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3717_ = lean_st_ref_get(v_a_3714_);
v_env_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc_ref(v_env_3718_);
lean_dec(v___x_3717_);
v___x_3719_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3720_ = lean_ctor_get(v___x_3719_, 0);
v_asyncMode_3721_ = lean_ctor_get(v_toEnvExtension_3720_, 2);
v___x_3722_ = 0;
v___x_3723_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3716_, v___x_3719_, v_env_3718_, v_declName_3713_, v_asyncMode_3721_, v___x_3722_);
if (lean_obj_tag(v___x_3723_) == 1)
{
lean_object* v_val_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3733_; 
v_val_3724_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3726_ = v___x_3723_;
v_isShared_3727_ = v_isSharedCheck_3733_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_val_3724_);
lean_dec(v___x_3723_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3733_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v_recArgPos_3728_; lean_object* v___x_3730_; 
v_recArgPos_3728_ = lean_ctor_get(v_val_3724_, 4);
lean_inc(v_recArgPos_3728_);
lean_dec(v_val_3724_);
if (v_isShared_3727_ == 0)
{
lean_ctor_set(v___x_3726_, 0, v_recArgPos_3728_);
v___x_3730_ = v___x_3726_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_recArgPos_3728_);
v___x_3730_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
lean_object* v___x_3731_; 
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
}
}
else
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_dec(v___x_3723_);
v___x_3734_ = lean_box(0);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
return v___x_3735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3736_, v_a_3737_);
lean_dec(v_a_3737_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
lean_object* v___x_3744_; 
lean_dec_ref(v_a_3741_);
v___x_3744_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3740_, v_a_3742_);
lean_dec(v_a_3742_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = lean_get_structural_rec_arg_pos(v_declName_3745_, v_a_3746_, v_a_3747_);
return v_res_3749_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_unsigned_to_nat(2295916746u);
v___x_3808_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3809_ = l_Lean_Name_num___override(v___x_3808_, v___x_3807_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3812_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3813_ = l_Lean_Name_str___override(v___x_3812_, v___x_3811_);
return v___x_3813_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3815_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3816_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3817_ = l_Lean_Name_str___override(v___x_3816_, v___x_3815_);
return v___x_3817_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = lean_unsigned_to_nat(2u);
v___x_3819_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3820_ = l_Lean_Name_num___override(v___x_3819_, v___x_3818_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3822_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3823_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3822_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_dec_ref_known(v___x_3823_, 1);
v___x_3824_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_3825_ = 0;
v___x_3826_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3827_ = l_Lean_registerTraceClass(v___x_3824_, v___x_3825_, v___x_3826_);
return v___x_3827_;
}
else
{
return v___x_3823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_3829_;
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
