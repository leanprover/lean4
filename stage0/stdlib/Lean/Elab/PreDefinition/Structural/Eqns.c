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
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
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
uint8_t l_Lean_isBRecOnRecursor(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 221, 148, 2, 30, 47, 242, 74)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 216, 81, 142, 241, 75, 113, 77)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_eqnInfoExt;
static lean_once_cell_t l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__0;
static lean_once_cell_t l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__1;
static lean_once_cell_t l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Structural_registerEqnsInfo___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 185, 97, 74, 150, 8, 57, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 19, 250, 232, 19, 103, 59, 84)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 64, 85, 238, 73, 235, 224, 238)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 241, 197, 13, 174, 23, 186, 239)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(123, 232, 160, 88, 66, 78, 213, 243)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 117, 235, 94, 194, 72, 147, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 146, 13, 135, 45, 158, 59, 107)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 222, 70, 43, 201, 77, 119, 184)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 51, 79, 28, 160, 228, 197, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(130, 14, 83, 143, 58, 41, 180, 194)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 131, 204, 33, 154, 17, 78, 114)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 169, 96, 182, 175, 131, 16, 69)}};
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
lean_object* v___x_228_; lean_object* v_env_229_; lean_object* v___x_230_; lean_object* v_toCold_231_; lean_object* v_mctx_232_; lean_object* v_lctx_233_; lean_object* v_options_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = lean_st_ref_get(v___y_224_);
v_toCold_231_ = lean_ctor_get(v___y_225_, 0);
v_mctx_232_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_mctx_232_);
lean_dec(v___x_230_);
v_lctx_233_ = lean_ctor_get(v___y_223_, 2);
v_options_234_ = lean_ctor_get(v_toCold_231_, 2);
lean_inc_ref(v_options_234_);
lean_inc_ref(v_lctx_233_);
v___x_235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_235_, 0, v_env_229_);
lean_ctor_set(v___x_235_, 1, v_mctx_232_);
lean_ctor_set(v___x_235_, 2, v_lctx_233_);
lean_ctor_set(v___x_235_, 3, v_options_234_);
v___x_236_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_msgData_222_);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0___boxed(lean_object* v_msgData_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msgData_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(lean_object* v_msg_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_ref_251_; lean_object* v___x_252_; lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_ref_251_ = lean_ctor_get(v___y_248_, 2);
v___x_252_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_inc(v_ref_251_);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_ref_251_);
lean_ctor_set(v___x_257_, 1, v_a_253_);
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 1);
lean_ctor_set(v___x_255_, 0, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg___boxed(lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(lean_object* v_xs_269_, lean_object* v_x_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_array_get_size(v_xs_269_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed(lean_object* v_xs_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(v_xs_278_, v_x_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec_ref(v_x_279_);
lean_dec_ref(v_xs_278_);
return v_res_285_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_286_; lean_object* v_dummy_287_; 
v___x_286_ = lean_box(0);
v_dummy_287_ = l_Lean_Expr_sort___override(v___x_286_);
return v_dummy_287_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__0));
v___x_290_ = l_Lean_stringToMessageData(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(lean_object* v_e_295_, lean_object* v_k_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; lean_object* v___y_309_; 
if (lean_obj_tag(v_x_297_) == 5)
{
lean_object* v_fn_314_; lean_object* v_arg_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_fn_314_ = lean_ctor_get(v_x_297_, 0);
lean_inc_ref(v_fn_314_);
v_arg_315_ = lean_ctor_get(v_x_297_, 1);
lean_inc_ref(v_arg_315_);
lean_dec_ref_known(v_x_297_, 2);
v___x_316_ = lean_array_set(v_x_298_, v_x_299_, v_arg_315_);
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_sub(v_x_299_, v___x_317_);
lean_dec(v_x_299_);
v_x_297_ = v_fn_314_;
v_x_298_ = v___x_316_;
v_x_299_ = v___x_318_;
goto _start;
}
else
{
lean_dec(v_x_299_);
if (lean_obj_tag(v_x_297_) == 11)
{
lean_object* v_typeName_320_; lean_object* v_idx_321_; lean_object* v_struct_322_; lean_object* v___f_323_; lean_object* v___x_324_; 
lean_dec_ref(v_e_295_);
v_typeName_320_ = lean_ctor_get(v_x_297_, 0);
lean_inc(v_typeName_320_);
v_idx_321_ = lean_ctor_get(v_x_297_, 1);
lean_inc(v_idx_321_);
v_struct_322_ = lean_ctor_get(v_x_297_, 2);
lean_inc_ref(v_struct_322_);
lean_dec_ref_known(v_x_297_, 3);
v___f_323_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_323_, 0, v_typeName_320_);
lean_closure_set(v___f_323_, 1, v_idx_321_);
lean_closure_set(v___f_323_, 2, v_x_298_);
lean_closure_set(v___f_323_, 3, v_k_296_);
v___x_324_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_struct_322_, v___f_323_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_324_;
}
else
{
if (lean_obj_tag(v_x_297_) == 4)
{
lean_object* v_declName_325_; lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; 
v_declName_325_ = lean_ctor_get(v_x_297_, 0);
v___x_326_ = lean_st_ref_get(v___y_303_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
lean_inc(v_declName_325_);
v___x_328_ = l_Lean_isBRecOnRecursor(v_env_327_, v_declName_325_);
if (v___x_328_ == 0)
{
lean_dec_ref_known(v_x_297_, 2);
lean_dec_ref(v_x_298_);
lean_dec_ref(v_k_296_);
v___y_306_ = v___y_300_;
v___y_307_ = v___y_301_;
v___y_308_ = v___y_302_;
v___y_309_ = v___y_303_;
goto v___jp_305_;
}
else
{
lean_object* v___x_329_; 
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
lean_inc_ref(v_x_297_);
v___x_329_ = lean_infer_type(v_x_297_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___f_331_; uint8_t v___x_332_; lean_object* v___x_333_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v___f_331_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2));
v___x_332_ = 0;
v___x_333_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_a_330_, v___f_331_, v___x_332_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = lean_array_get_size(v_x_298_);
v___x_336_ = lean_nat_dec_le(v_a_334_, v___x_335_);
if (v___x_336_ == 0)
{
lean_dec(v_a_334_);
lean_dec_ref_known(v_x_297_, 2);
lean_dec_ref(v_x_298_);
lean_dec_ref(v_k_296_);
v___y_306_ = v___y_300_;
v___y_307_ = v___y_301_;
v___y_308_ = v___y_302_;
v___y_309_ = v___y_303_;
goto v___jp_305_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_e_295_);
v___x_337_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_334_);
lean_inc_ref(v_x_298_);
v___x_338_ = l_Array_toSubarray___redArg(v_x_298_, v___x_337_, v_a_334_);
v___x_339_ = l_Subarray_copy___redArg(v___x_338_);
v___x_340_ = l_Lean_mkAppN(v_x_297_, v___x_339_);
lean_dec_ref(v___x_339_);
lean_inc(v___y_303_);
lean_inc_ref(v___y_302_);
lean_inc(v___y_301_);
lean_inc_ref(v___y_300_);
lean_inc_ref(v___x_340_);
v___x_341_ = lean_infer_type(v___x_340_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = l_Array_toSubarray___redArg(v_x_298_, v_a_334_, v___x_335_);
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_344_, 0, v___x_343_);
lean_closure_set(v___f_344_, 1, v_k_296_);
lean_closure_set(v___f_344_, 2, v___x_340_);
v___x_345_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4));
v___x_346_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v___x_345_, v_a_342_, v___f_344_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
return v___x_346_;
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v___x_340_);
lean_dec(v_a_334_);
lean_dec_ref(v_x_298_);
lean_dec_ref(v_k_296_);
v_a_347_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_341_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_341_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec_ref_known(v_x_297_, 2);
lean_dec_ref(v_x_298_);
lean_dec_ref(v_k_296_);
lean_dec_ref(v_e_295_);
v_a_355_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_333_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_333_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref_known(v_x_297_, 2);
lean_dec_ref(v_x_298_);
lean_dec_ref(v_k_296_);
lean_dec_ref(v_e_295_);
v_a_363_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_329_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_329_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_298_);
lean_dec_ref(v_x_297_);
lean_dec_ref(v_k_296_);
v___y_306_ = v___y_300_;
v___y_307_ = v___y_301_;
v___y_308_ = v___y_302_;
v___y_309_ = v___y_303_;
goto v___jp_305_;
}
}
}
v___jp_305_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1);
v___x_311_ = l_Lean_indentExpr(v_e_295_);
v___x_312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_312_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
return v___x_313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(lean_object* v_e_371_, lean_object* v_k_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_dummy_378_; lean_object* v_nargs_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_dummy_378_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_379_ = l_Lean_Expr_getAppNumArgs(v_e_371_);
lean_inc(v_nargs_379_);
v___x_380_ = lean_mk_array(v_nargs_379_, v_dummy_378_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_sub(v_nargs_379_, v___x_381_);
lean_dec(v_nargs_379_);
lean_inc_ref(v_e_371_);
v___x_383_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_371_, v_k_372_, v_e_371_, v___x_380_, v___x_382_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___boxed(lean_object* v_e_384_, lean_object* v_k_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_384_, v_k_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object* v_e_392_, lean_object* v_k_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_392_, v_k_393_, v_x_394_, v_x_395_, v_x_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_object* v_00_u03b1_403_, lean_object* v_e_404_, lean_object* v_k_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_404_, v_k_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___boxed(lean_object* v_00_u03b1_412_, lean_object* v_e_413_, lean_object* v_k_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(v_00_u03b1_412_, v_e_413_, v_k_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_object* v_00_u03b1_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___boxed(lean_object* v_00_u03b1_429_, lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(v_00_u03b1_429_, v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_object* v_00_u03b1_437_, lean_object* v_name_438_, uint8_t v_bi_439_, lean_object* v_type_440_, lean_object* v_k_441_, uint8_t v_kind_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_438_, v_bi_439_, v_type_440_, v_k_441_, v_kind_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_449_, lean_object* v_name_450_, lean_object* v_bi_451_, lean_object* v_type_452_, lean_object* v_k_453_, lean_object* v_kind_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v_bi_boxed_460_; uint8_t v_kind_boxed_461_; lean_object* v_res_462_; 
v_bi_boxed_460_ = lean_unbox(v_bi_451_);
v_kind_boxed_461_ = lean_unbox(v_kind_454_);
v_res_462_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(v_00_u03b1_449_, v_name_450_, v_bi_boxed_460_, v_type_452_, v_k_453_, v_kind_boxed_461_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_object* v_00_u03b1_463_, lean_object* v_name_464_, lean_object* v_type_465_, lean_object* v_k_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v_name_464_, v_type_465_, v_k_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___boxed(lean_object* v_00_u03b1_473_, lean_object* v_name_474_, lean_object* v_type_475_, lean_object* v_k_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(v_00_u03b1_473_, v_name_474_, v_type_475_, v_k_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_object* v_00_u03b1_483_, lean_object* v_e_484_, lean_object* v_k_485_, lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_484_, v_k_485_, v_x_486_, v_x_487_, v_x_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___boxed(lean_object* v_00_u03b1_495_, lean_object* v_e_496_, lean_object* v_k_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(v_00_u03b1_495_, v_e_496_, v_k_497_, v_x_498_, v_x_499_, v_x_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object* v___x_507_, uint8_t v___x_508_, lean_object* v_brecOnApp_509_, lean_object* v_x_510_, lean_object* v_c_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Meta_mkEq(v_c_511_, v___x_507_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_mk_empty_array_with_capacity(v___x_519_);
v___x_521_ = lean_array_push(v___x_520_, v_x_510_);
v___x_522_ = 0;
v___x_523_ = 1;
v___x_524_ = l_Lean_Meta_mkLambdaFVars(v___x_521_, v_a_518_, v___x_522_, v___x_508_, v___x_522_, v___x_508_, v___x_523_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec_ref(v___x_521_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_533_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_533_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_brecOnApp_509_);
lean_ctor_set(v___x_529_, 1, v_a_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_brecOnApp_509_);
v_a_534_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_524_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_524_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v_x_510_);
lean_dec_ref(v_brecOnApp_509_);
v_a_542_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_517_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_517_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed(lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v_brecOnApp_552_, lean_object* v_x_553_, lean_object* v_c_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___x_645__boxed_560_; lean_object* v_res_561_; 
v___x_645__boxed_560_ = lean_unbox(v___x_551_);
v_res_561_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(v___x_550_, v___x_645__boxed_560_, v_brecOnApp_552_, v_x_553_, v_c_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_561_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3(void){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2));
v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(lean_object* v_goal_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_574_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_575_ = lean_unsigned_to_nat(3u);
v___x_576_ = l_Lean_Expr_isAppOfArity(v_goal_568_, v___x_574_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3);
v___x_578_ = l_Lean_indentExpr(v_goal_568_);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_579_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
v___x_581_ = l_Lean_Expr_appFn_x21(v_goal_568_);
v___x_582_ = l_Lean_Expr_appArg_x21(v___x_581_);
lean_dec_ref(v___x_581_);
v___x_583_ = l_Lean_Expr_appArg_x21(v_goal_568_);
lean_dec_ref(v_goal_568_);
v___x_584_ = lean_box(v___x_576_);
v___f_585_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed), 10, 2);
lean_closure_set(v___f_585_, 0, v___x_583_);
lean_closure_set(v___f_585_, 1, v___x_584_);
v___x_586_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v___x_582_, v___f_585_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
return v___x_586_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___boxed(lean_object* v_goal_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_goal_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(lean_object* v_mvarId_594_, lean_object* v_x_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_594_, v_x_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
v_a_610_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_601_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_618_, lean_object* v_x_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_618_, v_x_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_object* v_00_u03b1_626_, lean_object* v_mvarId_627_, lean_object* v_x_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_627_, v_x_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___boxed(lean_object* v_00_u03b1_635_, lean_object* v_mvarId_636_, lean_object* v_x_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(v_00_u03b1_635_, v_mvarId_636_, v_x_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_643_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(lean_object* v_declName_644_, lean_object* v_x_645_){
_start:
{
uint8_t v___x_646_; 
v___x_646_ = lean_name_eq(v_x_645_, v_declName_644_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed(lean_object* v_declName_647_, lean_object* v_x_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(v_declName_647_, v_x_648_);
lean_dec(v_x_648_);
lean_dec(v_declName_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(lean_object* v_mvarId_651_, lean_object* v___f_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
lean_inc(v_mvarId_651_);
v___x_658_ = l_Lean_MVarId_getType_x27(v_mvarId_651_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_728_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_728_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_728_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_728_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_664_ = lean_unsigned_to_nat(3u);
v___x_665_ = l_Lean_Expr_isAppOfArity(v_a_659_, v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_668_; 
lean_dec(v_a_659_);
lean_dec_ref(v___f_652_);
lean_dec(v_mvarId_651_);
v___x_666_ = lean_box(0);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_666_);
v___x_668_ = v___x_661_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
lean_del_object(v___x_661_);
v___x_670_ = l_Lean_Expr_appArg_x21(v_a_659_);
v___x_671_ = l_Lean_Expr_consumeMData(v___x_670_);
lean_dec_ref(v___x_670_);
v___x_672_ = 0;
v___x_673_ = l_Lean_Meta_delta_x3f(v___x_671_, v___f_652_, v___x_672_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_719_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_719_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_719_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_719_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
if (lean_obj_tag(v_a_674_) == 1)
{
lean_object* v_val_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_676_);
v_val_678_ = lean_ctor_get(v_a_674_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_714_ == 0)
{
v___x_680_ = v_a_674_;
v_isShared_681_ = v_isSharedCheck_714_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_val_678_);
lean_dec(v_a_674_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_714_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = l_Lean_Expr_appFn_x21(v_a_659_);
lean_dec(v_a_659_);
v___x_683_ = l_Lean_Expr_appArg_x21(v___x_682_);
lean_dec_ref(v___x_682_);
v___x_684_ = l_Lean_Meta_mkEq(v___x_683_, v_val_678_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_651_, v_a_685_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_697_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_697_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_697_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_697_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v_a_687_);
v___x_692_ = v___x_680_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_692_);
v___x_694_ = v___x_689_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
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
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_del_object(v___x_680_);
v_a_698_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_686_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_686_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_del_object(v___x_680_);
lean_dec(v_mvarId_651_);
v_a_706_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_684_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_684_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_a_674_);
lean_dec(v_a_659_);
lean_dec(v_mvarId_651_);
v___x_715_ = lean_box(0);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_715_);
v___x_717_ = v___x_676_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_a_659_);
lean_dec(v_mvarId_651_);
v_a_720_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_673_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_673_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v___f_652_);
lean_dec(v_mvarId_651_);
v_a_729_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_658_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_658_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object* v_mvarId_737_, lean_object* v___f_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(v_mvarId_737_, v___f_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object* v_mvarId_745_, lean_object* v_declName_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___f_752_; lean_object* v___f_753_; lean_object* v___x_754_; 
v___f_752_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_752_, 0, v_declName_746_);
lean_inc(v_mvarId_745_);
v___f_753_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_753_, 0, v_mvarId_745_);
lean_closure_set(v___f_753_, 1, v___f_752_);
v___x_754_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_745_, v___f_753_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object* v_mvarId_755_, lean_object* v_declName_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_755_, v_declName_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_762_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_763_ = lean_unsigned_to_nat(32u);
v___x_764_ = lean_mk_empty_array_with_capacity(v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_766_ = ((size_t)5ULL);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_unsigned_to_nat(32u);
v___x_769_ = lean_mk_empty_array_with_capacity(v___x_768_);
v___x_770_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0);
v___x_771_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___x_769_);
lean_ctor_set(v___x_771_, 2, v___x_767_);
lean_ctor_set(v___x_771_, 3, v___x_767_);
lean_ctor_set_usize(v___x_771_, 4, v___x_766_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; lean_object* v_traceState_775_; lean_object* v_traces_776_; lean_object* v___x_777_; lean_object* v_traceState_778_; lean_object* v_env_779_; lean_object* v_nextMacroScope_780_; lean_object* v_ngen_781_; lean_object* v_auxDeclNGen_782_; lean_object* v_cache_783_; lean_object* v_messages_784_; lean_object* v_infoState_785_; lean_object* v_snapshotTasks_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_805_; 
v___x_774_ = lean_st_ref_get(v___y_772_);
v_traceState_775_ = lean_ctor_get(v___x_774_, 4);
lean_inc_ref(v_traceState_775_);
lean_dec(v___x_774_);
v_traces_776_ = lean_ctor_get(v_traceState_775_, 0);
lean_inc_ref(v_traces_776_);
lean_dec_ref(v_traceState_775_);
v___x_777_ = lean_st_ref_take(v___y_772_);
v_traceState_778_ = lean_ctor_get(v___x_777_, 4);
v_env_779_ = lean_ctor_get(v___x_777_, 0);
v_nextMacroScope_780_ = lean_ctor_get(v___x_777_, 1);
v_ngen_781_ = lean_ctor_get(v___x_777_, 2);
v_auxDeclNGen_782_ = lean_ctor_get(v___x_777_, 3);
v_cache_783_ = lean_ctor_get(v___x_777_, 5);
v_messages_784_ = lean_ctor_get(v___x_777_, 6);
v_infoState_785_ = lean_ctor_get(v___x_777_, 7);
v_snapshotTasks_786_ = lean_ctor_get(v___x_777_, 8);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_805_ == 0)
{
v___x_788_ = v___x_777_;
v_isShared_789_ = v_isSharedCheck_805_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_snapshotTasks_786_);
lean_inc(v_infoState_785_);
lean_inc(v_messages_784_);
lean_inc(v_cache_783_);
lean_inc(v_traceState_778_);
lean_inc(v_auxDeclNGen_782_);
lean_inc(v_ngen_781_);
lean_inc(v_nextMacroScope_780_);
lean_inc(v_env_779_);
lean_dec(v___x_777_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_805_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint64_t v_tid_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_803_; 
v_tid_790_ = lean_ctor_get_uint64(v_traceState_778_, sizeof(void*)*1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_traceState_778_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v_traceState_778_, 0);
lean_dec(v_unused_804_);
v___x_792_ = v_traceState_778_;
v_isShared_793_ = v_isSharedCheck_803_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_traceState_778_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_803_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_794_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_794_);
v___x_796_ = v___x_792_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_794_);
lean_ctor_set_uint64(v_reuseFailAlloc_802_, sizeof(void*)*1, v_tid_790_);
v___x_796_ = v_reuseFailAlloc_802_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_798_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 4, v___x_796_);
v___x_798_ = v___x_788_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_env_779_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_nextMacroScope_780_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_ngen_781_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_auxDeclNGen_782_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_cache_783_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_messages_784_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_infoState_785_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v_snapshotTasks_786_);
v___x_798_ = v_reuseFailAlloc_801_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_st_ref_put(v___y_772_, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_traces_776_);
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___boxed(lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_806_);
lean_dec(v___y_806_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v_opts_821_, lean_object* v_opt_822_){
_start:
{
lean_object* v_name_823_; lean_object* v_defValue_824_; lean_object* v_map_825_; lean_object* v___x_826_; 
v_name_823_ = lean_ctor_get(v_opt_822_, 0);
v_defValue_824_ = lean_ctor_get(v_opt_822_, 1);
v_map_825_ = lean_ctor_get(v_opts_821_, 0);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_825_, v_name_823_);
if (lean_obj_tag(v___x_826_) == 0)
{
uint8_t v___x_827_; 
v___x_827_ = lean_unbox(v_defValue_824_);
return v___x_827_;
}
else
{
lean_object* v_val_828_; 
v_val_828_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v___x_826_, 1);
if (lean_obj_tag(v_val_828_) == 1)
{
uint8_t v_v_829_; 
v_v_829_ = lean_ctor_get_uint8(v_val_828_, 0);
lean_dec_ref_known(v_val_828_, 0);
return v_v_829_;
}
else
{
uint8_t v___x_830_; 
lean_dec(v_val_828_);
v___x_830_ = lean_unbox(v_defValue_824_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v_opts_831_, lean_object* v_opt_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_831_, v_opt_832_);
lean_dec_ref(v_opt_832_);
lean_dec_ref(v_opts_831_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* v_mvarId_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_845_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v_mvarId_838_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object* v_mvarId_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(v_mvarId_849_, v_x_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec_ref(v_x_850_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* v_____r_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object* v_____r_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_____r_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_871_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_872_; double v___x_873_; 
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_float_of_nat(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v_cls_877_, lean_object* v_msg_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_ref_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_930_; 
v_ref_884_ = lean_ctor_get(v___y_881_, 2);
v___x_885_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_930_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_930_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_930_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v_traceState_891_; lean_object* v_env_892_; lean_object* v_nextMacroScope_893_; lean_object* v_ngen_894_; lean_object* v_auxDeclNGen_895_; lean_object* v_cache_896_; lean_object* v_messages_897_; lean_object* v_infoState_898_; lean_object* v_snapshotTasks_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_929_; 
v___x_890_ = lean_st_ref_take(v___y_882_);
v_traceState_891_ = lean_ctor_get(v___x_890_, 4);
v_env_892_ = lean_ctor_get(v___x_890_, 0);
v_nextMacroScope_893_ = lean_ctor_get(v___x_890_, 1);
v_ngen_894_ = lean_ctor_get(v___x_890_, 2);
v_auxDeclNGen_895_ = lean_ctor_get(v___x_890_, 3);
v_cache_896_ = lean_ctor_get(v___x_890_, 5);
v_messages_897_ = lean_ctor_get(v___x_890_, 6);
v_infoState_898_ = lean_ctor_get(v___x_890_, 7);
v_snapshotTasks_899_ = lean_ctor_get(v___x_890_, 8);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_929_ == 0)
{
v___x_901_ = v___x_890_;
v_isShared_902_ = v_isSharedCheck_929_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snapshotTasks_899_);
lean_inc(v_infoState_898_);
lean_inc(v_messages_897_);
lean_inc(v_cache_896_);
lean_inc(v_traceState_891_);
lean_inc(v_auxDeclNGen_895_);
lean_inc(v_ngen_894_);
lean_inc(v_nextMacroScope_893_);
lean_inc(v_env_892_);
lean_dec(v___x_890_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_929_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
uint64_t v_tid_903_; lean_object* v_traces_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_928_; 
v_tid_903_ = lean_ctor_get_uint64(v_traceState_891_, sizeof(void*)*1);
v_traces_904_ = lean_ctor_get(v_traceState_891_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v_traceState_891_);
if (v_isSharedCheck_928_ == 0)
{
v___x_906_ = v_traceState_891_;
v_isShared_907_ = v_isSharedCheck_928_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_traces_904_);
lean_dec(v_traceState_891_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_928_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; double v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_908_ = lean_box(0);
v___x_909_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
v___x_910_ = 0;
v___x_911_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_912_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_912_, 0, v_cls_877_);
lean_ctor_set(v___x_912_, 1, v___x_908_);
lean_ctor_set(v___x_912_, 2, v___x_911_);
lean_ctor_set_float(v___x_912_, sizeof(void*)*3, v___x_909_);
lean_ctor_set_float(v___x_912_, sizeof(void*)*3 + 8, v___x_909_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*3 + 16, v___x_910_);
v___x_913_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2));
v___x_914_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v_a_886_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
lean_inc(v_ref_884_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_ref_884_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_PersistentArray_push___redArg(v_traces_904_, v___x_915_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_916_);
v___x_918_ = v___x_906_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_916_);
lean_ctor_set_uint64(v_reuseFailAlloc_927_, sizeof(void*)*1, v_tid_903_);
v___x_918_ = v_reuseFailAlloc_927_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
lean_object* v___x_920_; 
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 4, v___x_918_);
v___x_920_ = v___x_901_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_env_892_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_nextMacroScope_893_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v_ngen_894_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_auxDeclNGen_895_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_926_, 5, v_cache_896_);
lean_ctor_set(v_reuseFailAlloc_926_, 6, v_messages_897_);
lean_ctor_set(v_reuseFailAlloc_926_, 7, v_infoState_898_);
lean_ctor_set(v_reuseFailAlloc_926_, 8, v_snapshotTasks_899_);
v___x_920_ = v_reuseFailAlloc_926_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_921_ = lean_st_ref_put(v___y_882_, v___x_920_);
v___x_922_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_922_);
v___x_924_ = v___x_888_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_931_, lean_object* v_msg_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_931_, v_msg_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(lean_object* v_opts_939_, lean_object* v_opt_940_){
_start:
{
lean_object* v_name_941_; lean_object* v_defValue_942_; lean_object* v_map_943_; lean_object* v___x_944_; 
v_name_941_ = lean_ctor_get(v_opt_940_, 0);
v_defValue_942_ = lean_ctor_get(v_opt_940_, 1);
v_map_943_ = lean_ctor_get(v_opts_939_, 0);
v___x_944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_943_, v_name_941_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_inc(v_defValue_942_);
return v_defValue_942_;
}
else
{
lean_object* v_val_945_; 
v_val_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_val_945_);
lean_dec_ref_known(v___x_944_, 1);
if (lean_obj_tag(v_val_945_) == 3)
{
lean_object* v_v_946_; 
v_v_946_ = lean_ctor_get(v_val_945_, 0);
lean_inc(v_v_946_);
lean_dec_ref_known(v_val_945_, 1);
return v_v_946_;
}
else
{
lean_dec(v_val_945_);
lean_inc(v_defValue_942_);
return v_defValue_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8___boxed(lean_object* v_opts_947_, lean_object* v_opt_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_947_, v_opt_948_);
lean_dec_ref(v_opt_948_);
lean_dec_ref(v_opts_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(size_t v_sz_950_, size_t v_i_951_, lean_object* v_bs_952_){
_start:
{
uint8_t v___x_953_; 
v___x_953_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
if (v___x_953_ == 0)
{
return v_bs_952_;
}
else
{
lean_object* v_v_954_; lean_object* v_msg_955_; lean_object* v___x_956_; lean_object* v_bs_x27_957_; size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; 
v_v_954_ = lean_array_uget_borrowed(v_bs_952_, v_i_951_);
v_msg_955_ = lean_ctor_get(v_v_954_, 1);
lean_inc_ref(v_msg_955_);
v___x_956_ = lean_unsigned_to_nat(0u);
v_bs_x27_957_ = lean_array_uset(v_bs_952_, v_i_951_, v___x_956_);
v___x_958_ = ((size_t)1ULL);
v___x_959_ = lean_usize_add(v_i_951_, v___x_958_);
v___x_960_ = lean_array_uset(v_bs_x27_957_, v_i_951_, v_msg_955_);
v_i_951_ = v___x_959_;
v_bs_952_ = v___x_960_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_962_, lean_object* v_i_963_, lean_object* v_bs_964_){
_start:
{
size_t v_sz_boxed_965_; size_t v_i_boxed_966_; lean_object* v_res_967_; 
v_sz_boxed_965_ = lean_unbox_usize(v_sz_962_);
lean_dec(v_sz_962_);
v_i_boxed_966_ = lean_unbox_usize(v_i_963_);
lean_dec(v_i_963_);
v_res_967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_boxed_965_, v_i_boxed_966_, v_bs_964_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object* v_oldTraces_968_, lean_object* v_data_969_, lean_object* v_ref_970_, lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_toCold_977_; lean_object* v_currRecDepth_978_; lean_object* v_ref_979_; uint8_t v_diag_980_; uint8_t v_suppressElabErrors_981_; lean_object* v___x_982_; lean_object* v_traceState_983_; lean_object* v_traces_984_; lean_object* v_ref_985_; lean_object* v___x_986_; lean_object* v___x_987_; size_t v_sz_988_; size_t v___x_989_; lean_object* v___x_990_; lean_object* v_msg_991_; lean_object* v___x_992_; lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1030_; 
v_toCold_977_ = lean_ctor_get(v___y_974_, 0);
v_currRecDepth_978_ = lean_ctor_get(v___y_974_, 1);
v_ref_979_ = lean_ctor_get(v___y_974_, 2);
v_diag_980_ = lean_ctor_get_uint8(v___y_974_, sizeof(void*)*3);
v_suppressElabErrors_981_ = lean_ctor_get_uint8(v___y_974_, sizeof(void*)*3 + 1);
v___x_982_ = lean_st_ref_get(v___y_975_);
v_traceState_983_ = lean_ctor_get(v___x_982_, 4);
lean_inc_ref(v_traceState_983_);
lean_dec(v___x_982_);
v_traces_984_ = lean_ctor_get(v_traceState_983_, 0);
lean_inc_ref(v_traces_984_);
lean_dec_ref(v_traceState_983_);
v_ref_985_ = l_Lean_replaceRef(v_ref_970_, v_ref_979_);
lean_inc(v_currRecDepth_978_);
lean_inc_ref(v_toCold_977_);
v___x_986_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_986_, 0, v_toCold_977_);
lean_ctor_set(v___x_986_, 1, v_currRecDepth_978_);
lean_ctor_set(v___x_986_, 2, v_ref_985_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*3, v_diag_980_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*3 + 1, v_suppressElabErrors_981_);
v___x_987_ = l_Lean_PersistentArray_toArray___redArg(v_traces_984_);
lean_dec_ref(v_traces_984_);
v_sz_988_ = lean_array_size(v___x_987_);
v___x_989_ = ((size_t)0ULL);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_988_, v___x_989_, v___x_987_);
v_msg_991_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_991_, 0, v_data_969_);
lean_ctor_set(v_msg_991_, 1, v_msg_971_);
lean_ctor_set(v_msg_991_, 2, v___x_990_);
v___x_992_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_991_, v___y_972_, v___y_973_, v___x_986_, v___y_975_);
lean_dec_ref_known(v___x_986_, 3);
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1030_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1030_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v_traceState_998_; lean_object* v_env_999_; lean_object* v_nextMacroScope_1000_; lean_object* v_ngen_1001_; lean_object* v_auxDeclNGen_1002_; lean_object* v_cache_1003_; lean_object* v_messages_1004_; lean_object* v_infoState_1005_; lean_object* v_snapshotTasks_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1029_; 
v___x_997_ = lean_st_ref_take(v___y_975_);
v_traceState_998_ = lean_ctor_get(v___x_997_, 4);
v_env_999_ = lean_ctor_get(v___x_997_, 0);
v_nextMacroScope_1000_ = lean_ctor_get(v___x_997_, 1);
v_ngen_1001_ = lean_ctor_get(v___x_997_, 2);
v_auxDeclNGen_1002_ = lean_ctor_get(v___x_997_, 3);
v_cache_1003_ = lean_ctor_get(v___x_997_, 5);
v_messages_1004_ = lean_ctor_get(v___x_997_, 6);
v_infoState_1005_ = lean_ctor_get(v___x_997_, 7);
v_snapshotTasks_1006_ = lean_ctor_get(v___x_997_, 8);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1008_ = v___x_997_;
v_isShared_1009_ = v_isSharedCheck_1029_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_snapshotTasks_1006_);
lean_inc(v_infoState_1005_);
lean_inc(v_messages_1004_);
lean_inc(v_cache_1003_);
lean_inc(v_traceState_998_);
lean_inc(v_auxDeclNGen_1002_);
lean_inc(v_ngen_1001_);
lean_inc(v_nextMacroScope_1000_);
lean_inc(v_env_999_);
lean_dec(v___x_997_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1029_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint64_t v_tid_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1027_; 
v_tid_1010_ = lean_ctor_get_uint64(v_traceState_998_, sizeof(void*)*1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_traceState_998_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_traceState_998_, 0);
lean_dec(v_unused_1028_);
v___x_1012_ = v_traceState_998_;
v_isShared_1013_ = v_isSharedCheck_1027_;
goto v_resetjp_1011_;
}
else
{
lean_dec(v_traceState_998_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1027_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_ref_970_);
lean_ctor_set(v___x_1014_, 1, v_a_993_);
v___x_1015_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_968_, v___x_1014_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1015_);
lean_ctor_set_uint64(v_reuseFailAlloc_1026_, sizeof(void*)*1, v_tid_1010_);
v___x_1017_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v___x_1017_);
v___x_1019_ = v___x_1008_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_env_999_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_nextMacroScope_1000_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_ngen_1001_);
lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_auxDeclNGen_1002_);
lean_ctor_set(v_reuseFailAlloc_1025_, 4, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1025_, 5, v_cache_1003_);
lean_ctor_set(v_reuseFailAlloc_1025_, 6, v_messages_1004_);
lean_ctor_set(v_reuseFailAlloc_1025_, 7, v_infoState_1005_);
lean_ctor_set(v_reuseFailAlloc_1025_, 8, v_snapshotTasks_1006_);
v___x_1019_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1020_ = lean_st_ref_put(v___y_975_, v___x_1019_);
v___x_1021_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1021_);
v___x_1023_ = v___x_995_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object* v_oldTraces_1031_, lean_object* v_data_1032_, lean_object* v_ref_1033_, lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1031_, v_data_1032_, v_ref_1033_, v_msg_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(lean_object* v_x_1041_){
_start:
{
if (lean_obj_tag(v_x_1041_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
v_a_1043_ = lean_ctor_get(v_x_1041_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_x_1041_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v_x_1041_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v_x_1041_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
v_a_1051_ = lean_ctor_get(v_x_1041_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_x_1041_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v_x_1041_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v_x_1041_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set_tag(v___x_1053_, 0);
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg___boxed(lean_object* v_x_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object* v_e_1062_){
_start:
{
if (lean_obj_tag(v_e_1062_) == 0)
{
uint8_t v___x_1063_; 
v___x_1063_ = 2;
return v___x_1063_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = 0;
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object* v_e_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_e_1065_);
lean_dec_ref(v_e_1065_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1071_; double v___x_1072_; 
v___x_1071_ = lean_unsigned_to_nat(1000u);
v___x_1072_ = lean_float_of_nat(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_cls_1073_, uint8_t v_collapsed_1074_, lean_object* v_tag_1075_, lean_object* v_opts_1076_, uint8_t v_clsEnabled_1077_, lean_object* v_oldTraces_1078_, lean_object* v_msg_1079_, lean_object* v_resStartStop_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v_data_1091_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___y_1099_; lean_object* v_a_1100_; uint8_t v___y_1115_; double v___y_1146_; 
v_fst_1086_ = lean_ctor_get(v_resStartStop_1080_, 0);
lean_inc(v_fst_1086_);
v_snd_1087_ = lean_ctor_get(v_resStartStop_1080_, 1);
lean_inc(v_snd_1087_);
lean_dec_ref(v_resStartStop_1080_);
v_fst_1094_ = lean_ctor_get(v_snd_1087_, 0);
lean_inc(v_fst_1094_);
v_snd_1095_ = lean_ctor_get(v_snd_1087_, 1);
lean_inc(v_snd_1095_);
lean_dec(v_snd_1087_);
v___x_1096_ = l_Lean_trace_profiler;
v___x_1097_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1076_, v___x_1096_);
if (v___x_1097_ == 0)
{
v___y_1115_ = v___x_1097_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1152_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1076_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; double v___x_1155_; double v___x_1156_; double v___x_1157_; 
v___x_1153_ = l_Lean_trace_profiler_threshold;
v___x_1154_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1076_, v___x_1153_);
v___x_1155_ = lean_float_of_nat(v___x_1154_);
v___x_1156_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_1157_ = lean_float_div(v___x_1155_, v___x_1156_);
v___y_1146_ = v___x_1157_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; double v___x_1160_; 
v___x_1158_ = l_Lean_trace_profiler_threshold;
v___x_1159_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1076_, v___x_1158_);
v___x_1160_ = lean_float_of_nat(v___x_1159_);
v___y_1146_ = v___x_1160_;
goto v___jp_1145_;
}
}
v___jp_1088_:
{
lean_object* v___x_1092_; 
lean_inc(v___y_1090_);
v___x_1092_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1078_, v_data_1091_, v___y_1090_, v___y_1089_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1093_; 
lean_dec_ref_known(v___x_1092_, 1);
v___x_1093_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1086_);
return v___x_1093_;
}
else
{
lean_dec(v_fst_1086_);
return v___x_1092_;
}
}
v___jp_1098_:
{
uint8_t v_result_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; double v___x_1104_; lean_object* v_data_1105_; 
v_result_1101_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_fst_1086_);
v___x_1102_ = lean_box(v_result_1101_);
v___x_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1102_);
v___x_1104_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_1075_);
lean_inc_ref(v___x_1103_);
lean_inc(v_cls_1073_);
v_data_1105_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1105_, 0, v_cls_1073_);
lean_ctor_set(v_data_1105_, 1, v___x_1103_);
lean_ctor_set(v_data_1105_, 2, v_tag_1075_);
lean_ctor_set_float(v_data_1105_, sizeof(void*)*3, v___x_1104_);
lean_ctor_set_float(v_data_1105_, sizeof(void*)*3 + 8, v___x_1104_);
lean_ctor_set_uint8(v_data_1105_, sizeof(void*)*3 + 16, v_collapsed_1074_);
if (v___x_1097_ == 0)
{
lean_dec_ref_known(v___x_1103_, 1);
lean_dec(v_snd_1095_);
lean_dec(v_fst_1094_);
lean_dec_ref(v_tag_1075_);
lean_dec(v_cls_1073_);
v___y_1089_ = v_a_1100_;
v___y_1090_ = v___y_1099_;
v_data_1091_ = v_data_1105_;
goto v___jp_1088_;
}
else
{
lean_object* v_data_1106_; double v___x_1107_; double v___x_1108_; 
lean_dec_ref_known(v_data_1105_, 3);
v_data_1106_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1106_, 0, v_cls_1073_);
lean_ctor_set(v_data_1106_, 1, v___x_1103_);
lean_ctor_set(v_data_1106_, 2, v_tag_1075_);
v___x_1107_ = lean_unbox_float(v_fst_1094_);
lean_dec(v_fst_1094_);
lean_ctor_set_float(v_data_1106_, sizeof(void*)*3, v___x_1107_);
v___x_1108_ = lean_unbox_float(v_snd_1095_);
lean_dec(v_snd_1095_);
lean_ctor_set_float(v_data_1106_, sizeof(void*)*3 + 8, v___x_1108_);
lean_ctor_set_uint8(v_data_1106_, sizeof(void*)*3 + 16, v_collapsed_1074_);
v___y_1089_ = v_a_1100_;
v___y_1090_ = v___y_1099_;
v_data_1091_ = v_data_1106_;
goto v___jp_1088_;
}
}
v___jp_1109_:
{
lean_object* v_ref_1110_; lean_object* v___x_1111_; 
v_ref_1110_ = lean_ctor_get(v___y_1083_, 2);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v_fst_1086_);
v___x_1111_ = lean_apply_6(v_msg_1079_, v_fst_1086_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, lean_box(0));
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v___y_1099_ = v_ref_1110_;
v_a_1100_ = v_a_1112_;
goto v___jp_1098_;
}
else
{
lean_object* v___x_1113_; 
lean_dec_ref_known(v___x_1111_, 1);
v___x_1113_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_1099_ = v_ref_1110_;
v_a_1100_ = v___x_1113_;
goto v___jp_1098_;
}
}
v___jp_1114_:
{
if (v_clsEnabled_1077_ == 0)
{
if (v___y_1115_ == 0)
{
lean_object* v___x_1116_; lean_object* v_traceState_1117_; lean_object* v_env_1118_; lean_object* v_nextMacroScope_1119_; lean_object* v_ngen_1120_; lean_object* v_auxDeclNGen_1121_; lean_object* v_cache_1122_; lean_object* v_messages_1123_; lean_object* v_infoState_1124_; lean_object* v_snapshotTasks_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_snd_1095_);
lean_dec(v_fst_1094_);
lean_dec_ref(v_msg_1079_);
lean_dec_ref(v_tag_1075_);
lean_dec(v_cls_1073_);
v___x_1116_ = lean_st_ref_take(v___y_1084_);
v_traceState_1117_ = lean_ctor_get(v___x_1116_, 4);
v_env_1118_ = lean_ctor_get(v___x_1116_, 0);
v_nextMacroScope_1119_ = lean_ctor_get(v___x_1116_, 1);
v_ngen_1120_ = lean_ctor_get(v___x_1116_, 2);
v_auxDeclNGen_1121_ = lean_ctor_get(v___x_1116_, 3);
v_cache_1122_ = lean_ctor_get(v___x_1116_, 5);
v_messages_1123_ = lean_ctor_get(v___x_1116_, 6);
v_infoState_1124_ = lean_ctor_get(v___x_1116_, 7);
v_snapshotTasks_1125_ = lean_ctor_get(v___x_1116_, 8);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1127_ = v___x_1116_;
v_isShared_1128_ = v_isSharedCheck_1144_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_snapshotTasks_1125_);
lean_inc(v_infoState_1124_);
lean_inc(v_messages_1123_);
lean_inc(v_cache_1122_);
lean_inc(v_traceState_1117_);
lean_inc(v_auxDeclNGen_1121_);
lean_inc(v_ngen_1120_);
lean_inc(v_nextMacroScope_1119_);
lean_inc(v_env_1118_);
lean_dec(v___x_1116_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1144_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint64_t v_tid_1129_; lean_object* v_traces_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1143_; 
v_tid_1129_ = lean_ctor_get_uint64(v_traceState_1117_, sizeof(void*)*1);
v_traces_1130_ = lean_ctor_get(v_traceState_1117_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_traceState_1117_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1132_ = v_traceState_1117_;
v_isShared_1133_ = v_isSharedCheck_1143_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_traces_1130_);
lean_dec(v_traceState_1117_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1143_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1078_, v_traces_1130_);
lean_dec_ref(v_traces_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1134_);
lean_ctor_set_uint64(v_reuseFailAlloc_1142_, sizeof(void*)*1, v_tid_1129_);
v___x_1136_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 4, v___x_1136_);
v___x_1138_ = v___x_1127_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_env_1118_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_nextMacroScope_1119_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_ngen_1120_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_auxDeclNGen_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v_cache_1122_);
lean_ctor_set(v_reuseFailAlloc_1141_, 6, v_messages_1123_);
lean_ctor_set(v_reuseFailAlloc_1141_, 7, v_infoState_1124_);
lean_ctor_set(v_reuseFailAlloc_1141_, 8, v_snapshotTasks_1125_);
v___x_1138_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_st_ref_put(v___y_1084_, v___x_1138_);
v___x_1140_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1086_);
return v___x_1140_;
}
}
}
}
}
else
{
goto v___jp_1109_;
}
}
else
{
goto v___jp_1109_;
}
}
v___jp_1145_:
{
double v___x_1147_; double v___x_1148_; double v___x_1149_; uint8_t v___x_1150_; 
v___x_1147_ = lean_unbox_float(v_snd_1095_);
v___x_1148_ = lean_unbox_float(v_fst_1094_);
v___x_1149_ = lean_float_sub(v___x_1147_, v___x_1148_);
v___x_1150_ = lean_float_decLt(v___y_1146_, v___x_1149_);
v___y_1115_ = v___x_1150_;
goto v___jp_1114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_cls_1161_, lean_object* v_collapsed_1162_, lean_object* v_tag_1163_, lean_object* v_opts_1164_, lean_object* v_clsEnabled_1165_, lean_object* v_oldTraces_1166_, lean_object* v_msg_1167_, lean_object* v_resStartStop_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
uint8_t v_collapsed_boxed_1174_; uint8_t v_clsEnabled_boxed_1175_; lean_object* v_res_1176_; 
v_collapsed_boxed_1174_ = lean_unbox(v_collapsed_1162_);
v_clsEnabled_boxed_1175_ = lean_unbox(v_clsEnabled_1165_);
v_res_1176_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1161_, v_collapsed_boxed_1174_, v_tag_1163_, v_opts_1164_, v_clsEnabled_boxed_1175_, v_oldTraces_1166_, v_msg_1167_, v_resStartStop_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec_ref(v_opts_1164_);
return v_res_1176_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1179_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = lean_unsigned_to_nat(16u);
v___x_1184_ = lean_mk_array(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1);
v___x_1186_ = lean_unsigned_to_nat(0u);
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1188_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1189_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1190_ = 1;
v___x_1191_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1188_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*2, v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_unsigned_to_nat(32u);
v___x_1193_ = lean_mk_empty_array_with_capacity(v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
size_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1195_ = ((size_t)5ULL);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_unsigned_to_nat(32u);
v___x_1198_ = lean_mk_empty_array_with_capacity(v___x_1197_);
v___x_1199_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7);
v___x_1200_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___x_1198_);
lean_ctor_set(v___x_1200_, 2, v___x_1196_);
lean_ctor_set(v___x_1200_, 3, v___x_1196_);
lean_ctor_set_usize(v___x_1200_, 4, v___x_1195_);
return v___x_1200_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1202_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1203_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_ctor_set(v___x_1203_, 2, v___x_1202_);
lean_ctor_set(v___x_1203_, 3, v___x_1201_);
return v___x_1203_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9);
v___x_1208_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_declName_1210_, lean_object* v_as_1211_, size_t v_i_1212_, size_t v_stop_1213_, lean_object* v_b_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v___x_1220_; 
v___x_1220_ = lean_usize_dec_eq(v_i_1212_, v_stop_1213_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_array_uget_borrowed(v_as_1211_, v_i_1212_);
lean_inc(v___x_1221_);
lean_inc(v_declName_1210_);
v___x_1222_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1210_, v___x_1221_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; size_t v___x_1224_; size_t v___x_1225_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v___x_1224_ = ((size_t)1ULL);
v___x_1225_ = lean_usize_add(v_i_1212_, v___x_1224_);
v_i_1212_ = v___x_1225_;
v_b_1214_ = v_a_1223_;
goto _start;
}
else
{
lean_dec(v_declName_1210_);
return v___x_1222_;
}
}
else
{
lean_object* v___x_1227_; 
lean_dec(v_declName_1210_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v_b_1214_);
return v___x_1227_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v_cls_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_cls_1243_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1244_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_1245_ = l_Lean_Name_append(v___x_1244_, v_cls_1243_);
return v___x_1245_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1246_; double v___x_1247_; 
v___x_1246_ = lean_unsigned_to_nat(1000000000u);
v___x_1247_ = lean_float_of_nat(v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
return v___x_1250_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
return v___x_1259_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1262_ = l_Lean_stringToMessageData(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1263_, lean_object* v___x_1264_, lean_object* v_declName_1265_, lean_object* v_____r_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1272_ = lean_array_get_size(v_val_1263_);
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_nat_dec_lt(v___x_1264_, v___x_1272_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec(v_declName_1265_);
v___x_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
return v___x_1275_;
}
else
{
uint8_t v___x_1276_; 
v___x_1276_ = lean_nat_dec_le(v___x_1272_, v___x_1272_);
if (v___x_1276_ == 0)
{
if (v___x_1274_ == 0)
{
lean_object* v___x_1277_; 
lean_dec(v_declName_1265_);
v___x_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1273_);
return v___x_1277_;
}
else
{
size_t v___x_1278_; size_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = lean_usize_of_nat(v___x_1272_);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1265_, v_val_1263_, v___x_1278_, v___x_1279_, v___x_1273_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1280_;
}
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1272_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1265_, v_val_1263_, v___x_1281_, v___x_1282_, v___x_1273_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
return v___x_1283_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1299_, lean_object* v_mvarId_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_toCold_1312_; lean_object* v_options_1313_; uint8_t v_hasTrace_1314_; 
v_toCold_1312_ = lean_ctor_get(v_a_1303_, 0);
v_options_1313_ = lean_ctor_get(v_toCold_1312_, 2);
v_hasTrace_1314_ = lean_ctor_get_uint8(v_options_1313_, sizeof(void*)*1);
if (v_hasTrace_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_inc(v_mvarId_1300_);
v___x_1315_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1499_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1499_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1499_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
uint8_t v___x_1320_; 
v___x_1320_ = lean_unbox(v_a_1316_);
lean_dec(v_a_1316_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
lean_del_object(v___x_1318_);
lean_inc(v_mvarId_1300_);
v___x_1321_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1486_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1486_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1486_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_unbox(v_a_1322_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_del_object(v___x_1324_);
lean_inc(v_mvarId_1300_);
v___x_1327_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
if (lean_obj_tag(v_a_1328_) == 1)
{
lean_object* v_val_1329_; 
lean_dec(v_a_1322_);
lean_dec(v_mvarId_1300_);
v_val_1329_ = lean_ctor_get(v_a_1328_, 0);
lean_inc(v_val_1329_);
lean_dec_ref_known(v_a_1328_, 1);
v_mvarId_1300_ = v_val_1329_;
goto _start;
}
else
{
lean_object* v___x_1331_; 
lean_dec(v_a_1328_);
lean_inc(v_mvarId_1300_);
v___x_1331_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
if (lean_obj_tag(v_a_1332_) == 1)
{
lean_object* v_val_1333_; 
lean_dec(v_a_1322_);
lean_dec(v_mvarId_1300_);
v_val_1333_ = lean_ctor_get(v_a_1332_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v_a_1332_, 1);
v_mvarId_1300_ = v_val_1333_;
goto _start;
}
else
{
uint8_t v___x_1335_; lean_object* v___x_1336_; 
lean_dec(v_a_1332_);
v___x_1335_ = 1;
lean_inc(v_mvarId_1300_);
v___x_1336_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1300_, v___x_1335_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
if (lean_obj_tag(v_a_1337_) == 1)
{
lean_object* v_val_1338_; 
lean_dec(v_a_1322_);
lean_dec(v_mvarId_1300_);
v_val_1338_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref_known(v_a_1337_, 1);
v_mvarId_1300_ = v_val_1338_;
goto _start;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; uint8_t v___x_1346_; uint8_t v___x_1347_; uint8_t v___x_1348_; uint8_t v___x_1349_; uint8_t v___x_1350_; uint8_t v___x_1351_; uint8_t v___x_1352_; uint8_t v___x_1353_; uint8_t v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_a_1337_);
v___x_1340_ = lean_unsigned_to_nat(100000u);
v___x_1341_ = lean_unsigned_to_nat(2u);
v___x_1342_ = 0;
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1344_, 0, v___x_1340_);
lean_ctor_set(v___x_1344_, 1, v___x_1341_);
lean_ctor_set(v___x_1344_, 2, v___x_1343_);
v___x_1345_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3, v___x_1345_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 1, v___x_1335_);
v___x_1346_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 2, v___x_1346_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 3, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 4, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 5, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 6, v___x_1342_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 7, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 8, v___x_1335_);
v___x_1347_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 9, v___x_1347_);
v___x_1348_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 10, v___x_1348_);
v___x_1349_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 11, v___x_1349_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 12, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 13, v___x_1335_);
v___x_1350_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 14, v___x_1350_);
v___x_1351_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 15, v___x_1351_);
v___x_1352_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 16, v___x_1352_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 17, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 18, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 19, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 20, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 21, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 22, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 23, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 24, v___x_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 25, v___x_1335_);
v___x_1353_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 26, v___x_1353_);
v___x_1354_ = lean_unbox(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 27, v___x_1354_);
v___x_1355_ = lean_unbox(v_a_1322_);
lean_dec(v_a_1322_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*3 + 28, v___x_1355_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___x_1357_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1358_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1359_ = l_Lean_Options_empty;
v___x_1360_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1344_, v___x_1357_, v___x_1358_, v___x_1359_, v_a_1301_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v___x_1362_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1300_);
v___x_1363_ = l_Lean_Meta_simpTargetStar(v_mvarId_1300_, v_a_1361_, v___x_1357_, v___x_1343_, v___x_1362_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1441_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1441_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1441_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_fst_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1439_; 
v_fst_1368_ = lean_ctor_get(v_a_1364_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_a_1364_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_a_1364_, 1);
lean_dec(v_unused_1440_);
v___x_1370_ = v_a_1364_;
v_isShared_1371_ = v_isSharedCheck_1439_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_fst_1368_);
lean_dec(v_a_1364_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1439_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
switch(lean_obj_tag(v_fst_1368_))
{
case 0:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_del_object(v___x_1370_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v___x_1372_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1372_);
v___x_1374_ = v___x_1366_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1372_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
case 1:
{
lean_object* v___x_1376_; 
lean_del_object(v___x_1366_);
lean_inc(v_declName_1299_);
lean_inc(v_mvarId_1300_);
v___x_1376_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1300_, v_declName_1299_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
if (lean_obj_tag(v_a_1377_) == 1)
{
lean_object* v_val_1378_; 
lean_del_object(v___x_1370_);
lean_dec(v_mvarId_1300_);
v_val_1378_ = lean_ctor_get(v_a_1377_, 0);
lean_inc(v_val_1378_);
lean_dec_ref_known(v_a_1377_, 1);
v_mvarId_1300_ = v_val_1378_;
goto _start;
}
else
{
lean_object* v___x_1380_; 
lean_dec(v_a_1377_);
lean_inc(v_mvarId_1300_);
v___x_1380_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1420_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1420_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1420_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
if (lean_obj_tag(v_a_1381_) == 1)
{
lean_object* v_val_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; uint8_t v___x_1388_; 
lean_del_object(v___x_1370_);
lean_dec(v_mvarId_1300_);
v_val_1385_ = lean_ctor_get(v_a_1381_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v_a_1381_, 1);
v___x_1386_ = lean_array_get_size(v_val_1385_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_nat_dec_lt(v___x_1356_, v___x_1386_);
if (v___x_1388_ == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_val_1385_);
lean_dec(v_declName_1299_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1390_ = v___x_1383_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1387_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
uint8_t v___x_1392_; 
v___x_1392_ = lean_nat_dec_le(v___x_1386_, v___x_1386_);
if (v___x_1392_ == 0)
{
if (v___x_1388_ == 0)
{
lean_object* v___x_1394_; 
lean_dec(v_val_1385_);
lean_dec(v_declName_1299_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1394_ = v___x_1383_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1387_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
else
{
size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
lean_del_object(v___x_1383_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = lean_usize_of_nat(v___x_1386_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1299_, v_val_1385_, v___x_1396_, v___x_1397_, v___x_1387_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_val_1385_);
return v___x_1398_;
}
}
else
{
size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
lean_del_object(v___x_1383_);
v___x_1399_ = ((size_t)0ULL);
v___x_1400_ = lean_usize_of_nat(v___x_1386_);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1299_, v_val_1385_, v___x_1399_, v___x_1400_, v___x_1387_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_val_1385_);
return v___x_1401_;
}
}
}
else
{
lean_object* v___x_1402_; 
lean_del_object(v___x_1383_);
lean_dec(v_a_1381_);
lean_inc(v_mvarId_1300_);
v___x_1402_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1300_, v___x_1335_, v___x_1335_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
if (lean_obj_tag(v_a_1403_) == 1)
{
lean_object* v_val_1404_; lean_object* v___x_1405_; 
lean_del_object(v___x_1370_);
lean_dec(v_mvarId_1300_);
v_val_1404_ = lean_ctor_get(v_a_1403_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v_a_1403_, 1);
v___x_1405_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1299_, v_val_1404_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_a_1403_);
lean_dec(v_declName_1299_);
v___x_1406_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_mvarId_1300_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set_tag(v___x_1370_, 7);
lean_ctor_set(v___x_1370_, 1, v___x_1407_);
lean_ctor_set(v___x_1370_, 0, v___x_1406_);
v___x_1409_ = v___x_1370_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1409_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1410_;
}
}
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_del_object(v___x_1370_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1412_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1402_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1402_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_del_object(v___x_1370_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1421_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1380_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1380_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_del_object(v___x_1370_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1429_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1376_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1376_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1437_; 
lean_del_object(v___x_1370_);
lean_del_object(v___x_1366_);
lean_dec(v_mvarId_1300_);
v_mvarId_1437_ = lean_ctor_get(v_fst_1368_, 0);
lean_inc(v_mvarId_1437_);
lean_dec_ref_known(v_fst_1368_, 1);
v_mvarId_1300_ = v_mvarId_1437_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1442_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1363_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1363_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1450_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1360_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1360_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec(v_a_1322_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1458_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1336_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1336_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_a_1322_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1466_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1331_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1331_);
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
lean_dec(v_a_1322_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1474_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1327_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1327_);
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
else
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_dec(v_a_1322_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v___x_1482_ = lean_box(0);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1482_);
v___x_1484_ = v___x_1324_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1487_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1321_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1321_);
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
lean_object* v___x_1495_; lean_object* v___x_1497_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v___x_1495_ = lean_box(0);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1495_);
v___x_1497_ = v___x_1318_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1500_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1315_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1315_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1508_; lean_object* v___f_1509_; lean_object* v_cls_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v_a_1517_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v_a_1529_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v_a_1534_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v_a_1545_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v_a_1560_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v_a_1565_; lean_object* v___y_1568_; lean_object* v___y_1569_; lean_object* v___y_1570_; 
v_inheritedTraceOptions_1508_ = lean_ctor_get(v_toCold_1312_, 11);
lean_inc(v_mvarId_1300_);
v___f_1509_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1509_, 0, v_mvarId_1300_);
v_cls_1510_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1511_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1512_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1513_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1508_, v_options_1313_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = l_Lean_trace_profiler;
v___x_1853_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1313_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v___f_1509_);
lean_inc(v_mvarId_1300_);
v___x_1854_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; uint8_t v___x_1856_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = lean_unbox(v_a_1855_);
lean_dec(v_a_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_inc(v_mvarId_1300_);
v___x_1857_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; uint8_t v___x_1859_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v___x_1859_ = lean_unbox(v_a_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_inc(v_mvarId_1300_);
v___x_1860_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
if (lean_obj_tag(v_a_1861_) == 1)
{
lean_dec(v_a_1858_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1862_; 
v_val_1862_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_a_1861_, 1);
v_mvarId_1300_ = v_val_1862_;
goto _start;
}
else
{
lean_object* v_val_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_val_1864_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v_a_1861_, 1);
v___x_1865_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1866_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1865_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_dec_ref_known(v___x_1866_, 1);
v_mvarId_1300_ = v_val_1864_;
goto _start;
}
else
{
lean_dec(v_val_1864_);
lean_dec(v_declName_1299_);
return v___x_1866_;
}
}
}
else
{
lean_object* v___x_1868_; 
lean_dec(v_a_1861_);
lean_inc(v_mvarId_1300_);
v___x_1868_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
if (lean_obj_tag(v_a_1869_) == 1)
{
lean_dec(v_a_1858_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1870_; 
v_val_1870_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref_known(v_a_1869_, 1);
v_mvarId_1300_ = v_val_1870_;
goto _start;
}
else
{
lean_object* v_val_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_val_1872_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v_a_1869_, 1);
v___x_1873_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1874_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1873_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_dec_ref_known(v___x_1874_, 1);
v_mvarId_1300_ = v_val_1872_;
goto _start;
}
else
{
lean_dec(v_val_1872_);
lean_dec(v_declName_1299_);
return v___x_1874_;
}
}
}
else
{
lean_object* v___x_1876_; 
lean_dec(v_a_1869_);
lean_inc(v_mvarId_1300_);
v___x_1876_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1300_, v_hasTrace_1314_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
if (lean_obj_tag(v_a_1877_) == 1)
{
lean_dec(v_a_1858_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1878_; 
v_val_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_val_1878_);
lean_dec_ref_known(v_a_1877_, 1);
v_mvarId_1300_ = v_val_1878_;
goto _start;
}
else
{
lean_object* v_val_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_val_1880_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_val_1880_);
lean_dec_ref_known(v_a_1877_, 1);
v___x_1881_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1882_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1881_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_dec_ref_known(v___x_1882_, 1);
v_mvarId_1300_ = v_val_1880_;
goto _start;
}
else
{
lean_dec(v_val_1880_);
lean_dec(v_declName_1299_);
return v___x_1882_;
}
}
}
else
{
lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; uint8_t v___x_1890_; uint8_t v___x_1891_; uint8_t v___x_1892_; uint8_t v___x_1893_; uint8_t v___x_1894_; uint8_t v___x_1895_; uint8_t v___x_1896_; uint8_t v___x_1897_; uint8_t v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
lean_dec(v_a_1877_);
v___x_1884_ = lean_unsigned_to_nat(100000u);
v___x_1885_ = lean_unsigned_to_nat(2u);
v___x_1886_ = 0;
v___x_1887_ = lean_box(0);
v___x_1888_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1888_, 0, v___x_1884_);
lean_ctor_set(v___x_1888_, 1, v___x_1885_);
lean_ctor_set(v___x_1888_, 2, v___x_1887_);
v___x_1889_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3, v___x_1889_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 1, v_hasTrace_1314_);
v___x_1890_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 2, v___x_1890_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 3, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 4, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 5, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 6, v___x_1886_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 7, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 8, v_hasTrace_1314_);
v___x_1891_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 9, v___x_1891_);
v___x_1892_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 10, v___x_1892_);
v___x_1893_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 11, v___x_1893_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 12, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 13, v_hasTrace_1314_);
v___x_1894_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 14, v___x_1894_);
v___x_1895_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 15, v___x_1895_);
v___x_1896_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 16, v___x_1896_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 17, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 18, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 19, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 20, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 21, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 22, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 23, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 24, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 25, v_hasTrace_1314_);
v___x_1897_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 26, v___x_1897_);
v___x_1898_ = lean_unbox(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 27, v___x_1898_);
v___x_1899_ = lean_unbox(v_a_1858_);
lean_dec(v_a_1858_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*3 + 28, v___x_1899_);
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1902_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1903_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1904_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
lean_ctor_set_uint8(v___x_1904_, sizeof(void*)*2, v_hasTrace_1314_);
v___x_1905_ = l_Lean_Options_empty;
v___x_1906_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1888_, v___x_1901_, v___x_1904_, v___x_1905_, v_a_1301_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc(v_a_1907_);
lean_dec_ref_known(v___x_1906_, 1);
v___x_1908_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1300_);
v___x_1909_ = l_Lean_Meta_simpTargetStar(v_mvarId_1300_, v_a_1907_, v___x_1901_, v___x_1887_, v___x_1908_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_2008_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_2008_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_2008_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v_fst_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_2006_; 
v_fst_1914_ = lean_ctor_get(v_a_1910_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_a_1910_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v_a_1910_, 1);
lean_dec(v_unused_2007_);
v___x_1916_ = v_a_1910_;
v_isShared_1917_ = v_isSharedCheck_2006_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_fst_1914_);
lean_dec(v_a_1910_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_2006_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
switch(lean_obj_tag(v_fst_1914_))
{
case 0:
{
lean_del_object(v___x_1916_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_box(0);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1918_);
v___x_1920_ = v___x_1912_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
lean_del_object(v___x_1912_);
v___x_1922_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1923_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1922_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1923_;
}
}
case 1:
{
lean_object* v___x_1924_; 
lean_del_object(v___x_1912_);
lean_inc(v_declName_1299_);
lean_inc(v_mvarId_1300_);
v___x_1924_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1300_, v_declName_1299_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref_known(v___x_1924_, 1);
if (lean_obj_tag(v_a_1925_) == 1)
{
lean_del_object(v___x_1916_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1926_; 
v_val_1926_ = lean_ctor_get(v_a_1925_, 0);
lean_inc(v_val_1926_);
lean_dec_ref_known(v_a_1925_, 1);
v_mvarId_1300_ = v_val_1926_;
goto _start;
}
else
{
lean_object* v_val_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v_val_1928_ = lean_ctor_get(v_a_1925_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v_a_1925_, 1);
v___x_1929_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1930_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1929_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_dec_ref_known(v___x_1930_, 1);
v_mvarId_1300_ = v_val_1928_;
goto _start;
}
else
{
lean_dec(v_val_1928_);
lean_dec(v_declName_1299_);
return v___x_1930_;
}
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_a_1925_);
lean_inc(v_mvarId_1300_);
v___x_1932_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1983_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1983_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1983_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
if (lean_obj_tag(v_a_1933_) == 1)
{
lean_object* v_val_1937_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; 
lean_del_object(v___x_1916_);
lean_dec(v_mvarId_1300_);
v_val_1937_ = lean_ctor_get(v_a_1933_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v_a_1933_, 1);
if (v___x_1513_ == 0)
{
v___y_1939_ = v_a_1301_;
v___y_1940_ = v_a_1302_;
v___y_1941_ = v_a_1303_;
v___y_1942_ = v_a_1304_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1960_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1959_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_dec_ref_known(v___x_1960_, 1);
v___y_1939_ = v_a_1301_;
v___y_1940_ = v_a_1302_;
v___y_1941_ = v_a_1303_;
v___y_1942_ = v_a_1304_;
goto v___jp_1938_;
}
else
{
lean_dec(v_val_1937_);
lean_del_object(v___x_1935_);
lean_dec(v_declName_1299_);
return v___x_1960_;
}
}
v___jp_1938_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = lean_array_get_size(v_val_1937_);
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_nat_dec_lt(v___x_1900_, v___x_1943_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1947_; 
lean_dec(v_val_1937_);
lean_dec(v_declName_1299_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1944_);
v___x_1947_ = v___x_1935_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1944_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
else
{
uint8_t v___x_1949_; 
v___x_1949_ = lean_nat_dec_le(v___x_1943_, v___x_1943_);
if (v___x_1949_ == 0)
{
if (v___x_1945_ == 0)
{
lean_object* v___x_1951_; 
lean_dec(v_val_1937_);
lean_dec(v_declName_1299_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1944_);
v___x_1951_ = v___x_1935_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1944_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
else
{
size_t v___x_1953_; size_t v___x_1954_; lean_object* v___x_1955_; 
lean_del_object(v___x_1935_);
v___x_1953_ = ((size_t)0ULL);
v___x_1954_ = lean_usize_of_nat(v___x_1943_);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1299_, v_val_1937_, v___x_1953_, v___x_1954_, v___x_1944_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v_val_1937_);
return v___x_1955_;
}
}
else
{
size_t v___x_1956_; size_t v___x_1957_; lean_object* v___x_1958_; 
lean_del_object(v___x_1935_);
v___x_1956_ = ((size_t)0ULL);
v___x_1957_ = lean_usize_of_nat(v___x_1943_);
v___x_1958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1299_, v_val_1937_, v___x_1956_, v___x_1957_, v___x_1944_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v_val_1937_);
return v___x_1958_;
}
}
}
}
else
{
lean_object* v___x_1961_; 
lean_del_object(v___x_1935_);
lean_dec(v_a_1933_);
lean_inc(v_mvarId_1300_);
v___x_1961_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1300_, v_hasTrace_1314_, v_hasTrace_1314_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
if (lean_obj_tag(v_a_1962_) == 1)
{
lean_del_object(v___x_1916_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1963_; lean_object* v___x_1964_; 
v_val_1963_ = lean_ctor_get(v_a_1962_, 0);
lean_inc(v_val_1963_);
lean_dec_ref_known(v_a_1962_, 1);
v___x_1964_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1299_, v_val_1963_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1964_;
}
else
{
lean_object* v_val_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_val_1965_ = lean_ctor_get(v_a_1962_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v_a_1962_, 1);
v___x_1966_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1967_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1966_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref_known(v___x_1967_, 1);
v___x_1968_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1299_, v_val_1965_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1968_;
}
else
{
lean_dec(v_val_1965_);
lean_dec(v_declName_1299_);
return v___x_1967_;
}
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
lean_dec(v_a_1962_);
lean_dec(v_declName_1299_);
v___x_1969_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1970_, 0, v_mvarId_1300_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set_tag(v___x_1916_, 7);
lean_ctor_set(v___x_1916_, 1, v___x_1970_);
lean_ctor_set(v___x_1916_, 0, v___x_1969_);
v___x_1972_ = v___x_1916_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; 
v___x_1973_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1972_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1973_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_del_object(v___x_1916_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1975_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1961_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1961_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_del_object(v___x_1916_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1984_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1932_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1932_);
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
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_del_object(v___x_1916_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1992_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1924_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1924_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
default: 
{
lean_del_object(v___x_1916_);
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_mvarId_2000_; 
v_mvarId_2000_ = lean_ctor_get(v_fst_1914_, 0);
lean_inc(v_mvarId_2000_);
lean_dec_ref_known(v_fst_1914_, 1);
v_mvarId_1300_ = v_mvarId_2000_;
goto _start;
}
else
{
lean_object* v_mvarId_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_mvarId_2002_ = lean_ctor_get(v_fst_1914_, 0);
lean_inc(v_mvarId_2002_);
lean_dec_ref_known(v_fst_1914_, 1);
v___x_2003_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2004_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_2003_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_dec_ref_known(v___x_2004_, 1);
v_mvarId_1300_ = v_mvarId_2002_;
goto _start;
}
else
{
lean_dec(v_mvarId_2002_);
lean_dec(v_declName_1299_);
return v___x_2004_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_2009_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1909_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1909_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_2017_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1906_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1906_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v_a_1858_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_2025_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1876_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1876_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
lean_dec(v_a_1858_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_2033_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1868_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1868_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_a_1858_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_2041_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_1860_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_1860_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_dec(v_a_1858_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
goto v___jp_1309_;
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2050_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_2049_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_dec_ref_known(v___x_2050_, 1);
goto v___jp_1309_;
}
else
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_2051_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1857_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1857_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
goto v___jp_1306_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2060_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_2059_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_dec_ref_known(v___x_2060_, 1);
goto v___jp_1306_;
}
else
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_2061_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_1854_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_1854_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
goto v___jp_1573_;
}
}
else
{
goto v___jp_1573_;
}
v___jp_1514_:
{
lean_object* v___x_1518_; double v___x_1519_; double v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1518_ = lean_io_get_num_heartbeats();
v___x_1519_ = lean_float_of_nat(v___y_1516_);
v___x_1520_ = lean_float_of_nat(v___x_1518_);
v___x_1521_ = lean_box_float(v___x_1519_);
v___x_1522_ = lean_box_float(v___x_1520_);
v___x_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_a_1517_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1510_, v_hasTrace_1314_, v___x_1511_, v_options_1313_, v___x_1513_, v___y_1515_, v___f_1509_, v___x_1524_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1525_;
}
v___jp_1526_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1529_);
v___y_1515_ = v___y_1527_;
v___y_1516_ = v___y_1528_;
v_a_1517_ = v___x_1530_;
goto v___jp_1514_;
}
v___jp_1531_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1534_);
v___y_1515_ = v___y_1532_;
v___y_1516_ = v___y_1533_;
v_a_1517_ = v___x_1535_;
goto v___jp_1514_;
}
v___jp_1536_:
{
if (lean_obj_tag(v___y_1539_) == 0)
{
lean_object* v_a_1540_; 
v_a_1540_ = lean_ctor_get(v___y_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___y_1539_, 1);
v___y_1532_ = v___y_1537_;
v___y_1533_ = v___y_1538_;
v_a_1534_ = v_a_1540_;
goto v___jp_1531_;
}
else
{
lean_object* v_a_1541_; 
v_a_1541_ = lean_ctor_get(v___y_1539_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___y_1539_, 1);
v___y_1527_ = v___y_1537_;
v___y_1528_ = v___y_1538_;
v_a_1529_ = v_a_1541_;
goto v___jp_1526_;
}
}
v___jp_1542_:
{
lean_object* v___x_1546_; double v___x_1547_; double v___x_1548_; double v___x_1549_; double v___x_1550_; double v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1546_ = lean_io_mono_nanos_now();
v___x_1547_ = lean_float_of_nat(v___y_1543_);
v___x_1548_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1549_ = lean_float_div(v___x_1547_, v___x_1548_);
v___x_1550_ = lean_float_of_nat(v___x_1546_);
v___x_1551_ = lean_float_div(v___x_1550_, v___x_1548_);
v___x_1552_ = lean_box_float(v___x_1549_);
v___x_1553_ = lean_box_float(v___x_1551_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1552_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_a_1545_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1510_, v_hasTrace_1314_, v___x_1511_, v_options_1313_, v___x_1513_, v___y_1544_, v___f_1509_, v___x_1555_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
return v___x_1556_;
}
v___jp_1557_:
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_a_1560_);
v___y_1543_ = v___y_1558_;
v___y_1544_ = v___y_1559_;
v_a_1545_ = v___x_1561_;
goto v___jp_1542_;
}
v___jp_1562_:
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_a_1565_);
v___y_1543_ = v___y_1563_;
v___y_1544_ = v___y_1564_;
v_a_1545_ = v___x_1566_;
goto v___jp_1542_;
}
v___jp_1567_:
{
if (lean_obj_tag(v___y_1570_) == 0)
{
lean_object* v_a_1571_; 
v_a_1571_ = lean_ctor_get(v___y_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___y_1570_, 1);
v___y_1558_ = v___y_1568_;
v___y_1559_ = v___y_1569_;
v_a_1560_ = v_a_1571_;
goto v___jp_1557_;
}
else
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___y_1570_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___y_1570_, 1);
v___y_1563_ = v___y_1568_;
v___y_1564_ = v___y_1569_;
v_a_1565_ = v_a_1572_;
goto v___jp_1562_;
}
}
v___jp_1573_:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1304_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1576_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1577_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1313_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1578_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1300_);
v___x_1579_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; uint8_t v___x_1581_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v___x_1579_, 1);
v___x_1581_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_inc(v_mvarId_1300_);
v___x_1582_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; uint8_t v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = lean_unbox(v_a_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
lean_inc(v_mvarId_1300_);
v___x_1585_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v___x_1585_, 1);
if (lean_obj_tag(v_a_1586_) == 1)
{
lean_dec(v_a_1583_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1587_; lean_object* v___x_1588_; 
v_val_1587_ = lean_ctor_get(v_a_1586_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v_a_1586_, 1);
v___x_1588_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1587_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1588_;
goto v___jp_1567_;
}
else
{
lean_object* v_val_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_val_1589_ = lean_ctor_get(v_a_1586_, 0);
lean_inc(v_val_1589_);
lean_dec_ref_known(v_a_1586_, 1);
v___x_1590_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1591_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1590_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v___x_1592_; 
lean_dec_ref_known(v___x_1591_, 1);
v___x_1592_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1589_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1592_;
goto v___jp_1567_;
}
else
{
lean_dec(v_val_1589_);
lean_dec(v_declName_1299_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1591_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1593_; 
lean_dec(v_a_1586_);
lean_inc(v_mvarId_1300_);
v___x_1593_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
if (lean_obj_tag(v_a_1594_) == 1)
{
lean_dec(v_a_1583_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1595_; lean_object* v___x_1596_; 
v_val_1595_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v_a_1594_, 1);
v___x_1596_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1595_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1596_;
goto v___jp_1567_;
}
else
{
lean_object* v_val_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_val_1597_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_val_1597_);
lean_dec_ref_known(v_a_1594_, 1);
v___x_1598_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1599_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1598_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v___x_1600_; 
lean_dec_ref_known(v___x_1599_, 1);
v___x_1600_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1597_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1600_;
goto v___jp_1567_;
}
else
{
lean_dec(v_val_1597_);
lean_dec(v_declName_1299_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1599_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1601_; 
lean_dec(v_a_1594_);
lean_inc(v_mvarId_1300_);
v___x_1601_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1300_, v_hasTrace_1314_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
if (lean_obj_tag(v_a_1602_) == 1)
{
lean_dec(v_a_1583_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1603_; lean_object* v___x_1604_; 
v_val_1603_ = lean_ctor_get(v_a_1602_, 0);
lean_inc(v_val_1603_);
lean_dec_ref_known(v_a_1602_, 1);
v___x_1604_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1603_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1604_;
goto v___jp_1567_;
}
else
{
lean_object* v_val_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_val_1605_ = lean_ctor_get(v_a_1602_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v_a_1602_, 1);
v___x_1606_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1607_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1606_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v___x_1608_; 
lean_dec_ref_known(v___x_1607_, 1);
v___x_1608_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1605_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1608_;
goto v___jp_1567_;
}
else
{
lean_dec(v_val_1605_);
lean_dec(v_declName_1299_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1607_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; uint8_t v___x_1615_; uint8_t v___x_1616_; uint8_t v___x_1617_; uint8_t v___x_1618_; uint8_t v___x_1619_; uint8_t v___x_1620_; uint8_t v___x_1621_; uint8_t v___x_1622_; uint8_t v___x_1623_; uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec(v_a_1602_);
v___x_1609_ = lean_unsigned_to_nat(100000u);
v___x_1610_ = lean_unsigned_to_nat(2u);
v___x_1611_ = 0;
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1613_, 0, v___x_1609_);
lean_ctor_set(v___x_1613_, 1, v___x_1610_);
lean_ctor_set(v___x_1613_, 2, v___x_1612_);
v___x_1614_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3, v___x_1614_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 1, v_hasTrace_1314_);
v___x_1615_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 2, v___x_1615_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 3, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 4, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 5, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 6, v___x_1611_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 7, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 8, v_hasTrace_1314_);
v___x_1616_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 9, v___x_1616_);
v___x_1617_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 10, v___x_1617_);
v___x_1618_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 11, v___x_1618_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 12, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 13, v_hasTrace_1314_);
v___x_1619_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 14, v___x_1619_);
v___x_1620_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 15, v___x_1620_);
v___x_1621_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 16, v___x_1621_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 17, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 18, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 19, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 20, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 21, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 22, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 23, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 24, v_hasTrace_1314_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 25, v_hasTrace_1314_);
v___x_1622_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 26, v___x_1622_);
v___x_1623_ = lean_unbox(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 27, v___x_1623_);
v___x_1624_ = lean_unbox(v_a_1583_);
lean_dec(v_a_1583_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*3 + 28, v___x_1624_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1627_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1628_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1629_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
lean_ctor_set_uint8(v___x_1629_, sizeof(void*)*2, v_hasTrace_1314_);
v___x_1630_ = l_Lean_Options_empty;
v___x_1631_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1613_, v___x_1626_, v___x_1629_, v___x_1630_, v_a_1301_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v___x_1631_, 1);
v___x_1633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1300_);
v___x_1634_ = l_Lean_Meta_simpTargetStar(v_mvarId_1300_, v_a_1632_, v___x_1626_, v___x_1612_, v___x_1633_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v_fst_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1690_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v_fst_1636_ = lean_ctor_get(v_a_1635_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_a_1635_);
if (v_isSharedCheck_1690_ == 0)
{
lean_object* v_unused_1691_; 
v_unused_1691_ = lean_ctor_get(v_a_1635_, 1);
lean_dec(v_unused_1691_);
v___x_1638_ = v_a_1635_;
v_isShared_1639_ = v_isSharedCheck_1690_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_fst_1636_);
lean_dec(v_a_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1690_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
switch(lean_obj_tag(v_fst_1636_))
{
case 0:
{
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_box(0);
v___y_1558_ = v___x_1578_;
v___y_1559_ = v_a_1575_;
v_a_1560_ = v___x_1640_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1642_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1641_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1642_;
goto v___jp_1567_;
}
}
case 1:
{
lean_object* v___x_1643_; 
lean_inc(v_declName_1299_);
lean_inc(v_mvarId_1300_);
v___x_1643_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1300_, v_declName_1299_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
if (lean_obj_tag(v_a_1644_) == 1)
{
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1645_; lean_object* v___x_1646_; 
v_val_1645_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v_a_1644_, 1);
v___x_1646_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1645_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1646_;
goto v___jp_1567_;
}
else
{
lean_object* v_val_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_val_1647_ = lean_ctor_get(v_a_1644_, 0);
lean_inc(v_val_1647_);
lean_dec_ref_known(v_a_1644_, 1);
v___x_1648_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1649_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1648_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref_known(v___x_1649_, 1);
v___x_1650_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1647_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1650_;
goto v___jp_1567_;
}
else
{
lean_dec(v_val_1647_);
lean_dec(v_declName_1299_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1649_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1651_; 
lean_dec(v_a_1644_);
lean_inc(v_mvarId_1300_);
v___x_1651_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v___x_1651_, 1);
if (lean_obj_tag(v_a_1652_) == 1)
{
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_val_1653_ = lean_ctor_get(v_a_1652_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v_a_1652_, 1);
v___x_1654_ = lean_box(0);
v___x_1655_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1653_, v___x_1625_, v_declName_1299_, v___x_1654_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_val_1653_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1655_;
goto v___jp_1567_;
}
else
{
lean_object* v_val_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_val_1656_ = lean_ctor_get(v_a_1652_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v_a_1652_, 1);
v___x_1657_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1658_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1657_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1660_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1658_, 1);
v___x_1660_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1656_, v___x_1625_, v_declName_1299_, v_a_1659_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_val_1656_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1660_;
goto v___jp_1567_;
}
else
{
lean_dec(v_val_1656_);
lean_dec(v_declName_1299_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1658_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1661_; 
lean_dec(v_a_1652_);
lean_inc(v_mvarId_1300_);
v___x_1661_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1300_, v_hasTrace_1314_, v_hasTrace_1314_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1680_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1680_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1680_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
if (lean_obj_tag(v_a_1662_) == 1)
{
lean_del_object(v___x_1664_);
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1666_; lean_object* v___x_1667_; 
v_val_1666_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1666_);
lean_dec_ref_known(v_a_1662_, 1);
v___x_1667_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1299_, v_val_1666_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1667_;
goto v___jp_1567_;
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_val_1668_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1668_);
lean_dec_ref_known(v_a_1662_, 1);
v___x_1669_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1670_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1669_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1671_; 
lean_dec_ref_known(v___x_1670_, 1);
v___x_1671_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1299_, v_val_1668_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1671_;
goto v___jp_1567_;
}
else
{
lean_dec(v_val_1668_);
lean_dec(v_declName_1299_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1670_;
goto v___jp_1567_;
}
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_dec(v_a_1662_);
lean_dec(v_declName_1299_);
v___x_1672_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 1);
lean_ctor_set(v___x_1664_, 0, v_mvarId_1300_);
v___x_1674_ = v___x_1664_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_mvarId_1300_);
v___x_1674_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1676_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 7);
lean_ctor_set(v___x_1638_, 1, v___x_1674_);
lean_ctor_set(v___x_1638_, 0, v___x_1672_);
v___x_1676_ = v___x_1638_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1672_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1676_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1677_;
goto v___jp_1567_;
}
}
}
}
}
else
{
lean_object* v_a_1681_; 
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1681_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1661_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1681_;
goto v___jp_1562_;
}
}
}
else
{
lean_object* v_a_1682_; 
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1682_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1651_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1682_;
goto v___jp_1562_;
}
}
}
else
{
lean_object* v_a_1683_; 
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1683_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1643_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1683_;
goto v___jp_1562_;
}
}
default: 
{
lean_del_object(v___x_1638_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_mvarId_1684_; lean_object* v___x_1685_; 
v_mvarId_1684_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc(v_mvarId_1684_);
lean_dec_ref_known(v_fst_1636_, 1);
v___x_1685_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_mvarId_1684_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1685_;
goto v___jp_1567_;
}
else
{
lean_object* v_mvarId_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_mvarId_1686_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc(v_mvarId_1686_);
lean_dec_ref_known(v_fst_1636_, 1);
v___x_1687_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1688_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1687_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v___x_1689_; 
lean_dec_ref_known(v___x_1688_, 1);
v___x_1689_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_mvarId_1686_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1689_;
goto v___jp_1567_;
}
else
{
lean_dec(v_mvarId_1686_);
lean_dec(v_declName_1299_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1688_;
goto v___jp_1567_;
}
}
}
}
}
}
else
{
lean_object* v_a_1692_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1692_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1692_);
lean_dec_ref_known(v___x_1634_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1692_;
goto v___jp_1562_;
}
}
else
{
lean_object* v_a_1693_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1693_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1631_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1693_;
goto v___jp_1562_;
}
}
}
else
{
lean_object* v_a_1694_; 
lean_dec(v_a_1583_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1694_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1601_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1694_;
goto v___jp_1562_;
}
}
}
else
{
lean_object* v_a_1695_; 
lean_dec(v_a_1583_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1695_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1593_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1695_;
goto v___jp_1562_;
}
}
}
else
{
lean_object* v_a_1696_; 
lean_dec(v_a_1583_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1696_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1585_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1696_;
goto v___jp_1562_;
}
}
else
{
lean_dec(v_a_1583_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1697_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1698_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1700_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1699_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1702_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_a_1701_);
lean_dec_ref_known(v___x_1700_, 1);
v___x_1702_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1701_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1702_;
goto v___jp_1567_;
}
else
{
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1700_;
goto v___jp_1567_;
}
}
}
}
else
{
lean_object* v_a_1703_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1703_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1582_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1703_;
goto v___jp_1562_;
}
}
else
{
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_box(0);
v___x_1705_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1704_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1705_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1707_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1706_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1709_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
v___x_1709_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1708_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1709_;
goto v___jp_1567_;
}
else
{
v___y_1568_ = v___x_1578_;
v___y_1569_ = v_a_1575_;
v___y_1570_ = v___x_1707_;
goto v___jp_1567_;
}
}
}
}
else
{
lean_object* v_a_1710_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1710_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1579_, 1);
v___y_1563_ = v___x_1578_;
v___y_1564_ = v_a_1575_;
v_a_1565_ = v_a_1710_;
goto v___jp_1562_;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1300_);
v___x_1712_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; uint8_t v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = lean_unbox(v_a_1713_);
lean_dec(v_a_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_inc(v_mvarId_1300_);
v___x_1715_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; uint8_t v___x_1717_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v___x_1717_ = lean_unbox(v_a_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_inc(v_mvarId_1300_);
v___x_1718_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
if (lean_obj_tag(v_a_1719_) == 1)
{
lean_dec(v_a_1716_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1720_; lean_object* v___x_1721_; 
v_val_1720_ = lean_ctor_get(v_a_1719_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v_a_1719_, 1);
v___x_1721_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1720_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1721_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_val_1722_ = lean_ctor_get(v_a_1719_, 0);
lean_inc(v_val_1722_);
lean_dec_ref_known(v_a_1719_, 1);
v___x_1723_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1724_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1723_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref_known(v___x_1724_, 1);
v___x_1725_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1722_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1725_;
goto v___jp_1536_;
}
else
{
lean_dec(v_val_1722_);
lean_dec(v_declName_1299_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1724_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v___x_1726_; 
lean_dec(v_a_1719_);
lean_inc(v_mvarId_1300_);
v___x_1726_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
if (lean_obj_tag(v_a_1727_) == 1)
{
lean_dec(v_a_1716_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1728_; lean_object* v___x_1729_; 
v_val_1728_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v_val_1728_);
lean_dec_ref_known(v_a_1727_, 1);
v___x_1729_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1728_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1729_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_val_1730_ = lean_ctor_get(v_a_1727_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v_a_1727_, 1);
v___x_1731_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1732_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1731_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
lean_dec_ref_known(v___x_1732_, 1);
v___x_1733_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1730_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1733_;
goto v___jp_1536_;
}
else
{
lean_dec(v_val_1730_);
lean_dec(v_declName_1299_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1732_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v___x_1734_; 
lean_dec(v_a_1727_);
lean_inc(v_mvarId_1300_);
v___x_1734_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1300_, v___x_1577_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
if (lean_obj_tag(v_a_1735_) == 1)
{
lean_dec(v_a_1716_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1736_; lean_object* v___x_1737_; 
v_val_1736_ = lean_ctor_get(v_a_1735_, 0);
lean_inc(v_val_1736_);
lean_dec_ref_known(v_a_1735_, 1);
v___x_1737_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1736_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1737_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v_val_1738_ = lean_ctor_get(v_a_1735_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v_a_1735_, 1);
v___x_1739_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1740_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1739_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v___x_1741_; 
lean_dec_ref_known(v___x_1740_, 1);
v___x_1741_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1738_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1741_;
goto v___jp_1536_;
}
else
{
lean_dec(v_val_1738_);
lean_dec(v_declName_1299_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1740_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; uint8_t v___x_1747_; uint8_t v___x_1748_; uint8_t v___x_1749_; uint8_t v___x_1750_; uint8_t v___x_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_dec(v_a_1735_);
v___x_1742_ = lean_unsigned_to_nat(100000u);
v___x_1743_ = lean_unsigned_to_nat(2u);
v___x_1744_ = 0;
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1746_, 0, v___x_1742_);
lean_ctor_set(v___x_1746_, 1, v___x_1743_);
lean_ctor_set(v___x_1746_, 2, v___x_1745_);
v___x_1747_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3, v___x_1747_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 1, v___x_1577_);
v___x_1748_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 2, v___x_1748_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 3, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 4, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 5, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 6, v___x_1744_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 7, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 8, v___x_1577_);
v___x_1749_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 9, v___x_1749_);
v___x_1750_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 10, v___x_1750_);
v___x_1751_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 11, v___x_1751_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 12, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 13, v___x_1577_);
v___x_1752_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 14, v___x_1752_);
v___x_1753_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 15, v___x_1753_);
v___x_1754_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 16, v___x_1754_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 17, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 18, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 19, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 20, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 21, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 22, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 23, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 24, v___x_1577_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 25, v___x_1577_);
v___x_1755_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 26, v___x_1755_);
v___x_1756_ = lean_unbox(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 27, v___x_1756_);
v___x_1757_ = lean_unbox(v_a_1716_);
lean_dec(v_a_1716_);
lean_ctor_set_uint8(v___x_1746_, sizeof(void*)*3 + 28, v___x_1757_);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1760_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1761_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1762_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1760_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
lean_ctor_set_uint8(v___x_1762_, sizeof(void*)*2, v___x_1577_);
v___x_1763_ = l_Lean_Options_empty;
v___x_1764_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1746_, v___x_1759_, v___x_1762_, v___x_1763_, v_a_1301_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1300_);
v___x_1767_ = l_Lean_Meta_simpTargetStar(v_mvarId_1300_, v_a_1765_, v___x_1759_, v___x_1745_, v___x_1766_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v_fst_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1823_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v_fst_1769_ = lean_ctor_get(v_a_1768_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_a_1768_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_a_1768_, 1);
lean_dec(v_unused_1824_);
v___x_1771_ = v_a_1768_;
v_isShared_1772_ = v_isSharedCheck_1823_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_fst_1769_);
lean_dec(v_a_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1823_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
switch(lean_obj_tag(v_fst_1769_))
{
case 0:
{
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1773_; 
v___x_1773_ = lean_box(0);
v___y_1532_ = v_a_1575_;
v___y_1533_ = v___x_1711_;
v_a_1534_ = v___x_1773_;
goto v___jp_1531_;
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1775_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1774_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1775_;
goto v___jp_1536_;
}
}
case 1:
{
lean_object* v___x_1776_; 
lean_inc(v_declName_1299_);
lean_inc(v_mvarId_1300_);
v___x_1776_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1300_, v_declName_1299_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
if (lean_obj_tag(v_a_1777_) == 1)
{
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1778_; lean_object* v___x_1779_; 
v_val_1778_ = lean_ctor_get(v_a_1777_, 0);
lean_inc(v_val_1778_);
lean_dec_ref_known(v_a_1777_, 1);
v___x_1779_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1778_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1779_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_val_1780_ = lean_ctor_get(v_a_1777_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v_a_1777_, 1);
v___x_1781_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1782_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1781_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v___x_1783_; 
lean_dec_ref_known(v___x_1782_, 1);
v___x_1783_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_val_1780_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1783_;
goto v___jp_1536_;
}
else
{
lean_dec(v_val_1780_);
lean_dec(v_declName_1299_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1782_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v___x_1784_; 
lean_dec(v_a_1777_);
lean_inc(v_mvarId_1300_);
v___x_1784_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
if (lean_obj_tag(v_a_1785_) == 1)
{
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_val_1786_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1786_);
lean_dec_ref_known(v_a_1785_, 1);
v___x_1787_ = lean_box(0);
v___x_1788_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1786_, v___x_1758_, v_declName_1299_, v___x_1787_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_val_1786_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1788_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_val_1789_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v_a_1785_, 1);
v___x_1790_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1791_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1790_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_object* v_a_1792_; lean_object* v___x_1793_; 
v_a_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_a_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1789_, v___x_1758_, v_declName_1299_, v_a_1792_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
lean_dec(v_val_1789_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1793_;
goto v___jp_1536_;
}
else
{
lean_dec(v_val_1789_);
lean_dec(v_declName_1299_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1791_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v___x_1794_; 
lean_dec(v_a_1785_);
lean_inc(v_mvarId_1300_);
v___x_1794_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1300_, v___x_1577_, v___x_1577_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1813_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1813_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1813_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
if (lean_obj_tag(v_a_1795_) == 1)
{
lean_del_object(v___x_1797_);
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_val_1799_; lean_object* v___x_1800_; 
v_val_1799_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v_a_1795_, 1);
v___x_1800_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1299_, v_val_1799_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1800_;
goto v___jp_1536_;
}
else
{
lean_object* v_val_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_val_1801_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_val_1801_);
lean_dec_ref_known(v_a_1795_, 1);
v___x_1802_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1803_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1802_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref_known(v___x_1803_, 1);
v___x_1804_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1299_, v_val_1801_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1804_;
goto v___jp_1536_;
}
else
{
lean_dec(v_val_1801_);
lean_dec(v_declName_1299_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1803_;
goto v___jp_1536_;
}
}
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
lean_dec(v_a_1795_);
lean_dec(v_declName_1299_);
v___x_1805_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1798_ == 0)
{
lean_ctor_set_tag(v___x_1797_, 1);
lean_ctor_set(v___x_1797_, 0, v_mvarId_1300_);
v___x_1807_ = v___x_1797_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_mvarId_1300_);
v___x_1807_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1809_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 7);
lean_ctor_set(v___x_1771_, 1, v___x_1807_);
lean_ctor_set(v___x_1771_, 0, v___x_1805_);
v___x_1809_ = v___x_1771_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1809_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1810_;
goto v___jp_1536_;
}
}
}
}
}
else
{
lean_object* v_a_1814_; 
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1814_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1794_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1814_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1815_; 
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1815_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1784_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1815_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1816_; 
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1816_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1776_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1816_;
goto v___jp_1526_;
}
}
default: 
{
lean_del_object(v___x_1771_);
lean_dec(v_mvarId_1300_);
if (v___x_1513_ == 0)
{
lean_object* v_mvarId_1817_; lean_object* v___x_1818_; 
v_mvarId_1817_ = lean_ctor_get(v_fst_1769_, 0);
lean_inc(v_mvarId_1817_);
lean_dec_ref_known(v_fst_1769_, 1);
v___x_1818_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_mvarId_1817_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1818_;
goto v___jp_1536_;
}
else
{
lean_object* v_mvarId_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_mvarId_1819_ = lean_ctor_get(v_fst_1769_, 0);
lean_inc(v_mvarId_1819_);
lean_dec_ref_known(v_fst_1769_, 1);
v___x_1820_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1821_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1820_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v___x_1822_; 
lean_dec_ref_known(v___x_1821_, 1);
v___x_1822_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1299_, v_mvarId_1819_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1822_;
goto v___jp_1536_;
}
else
{
lean_dec(v_mvarId_1819_);
lean_dec(v_declName_1299_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1821_;
goto v___jp_1536_;
}
}
}
}
}
}
else
{
lean_object* v_a_1825_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1825_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1767_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1825_;
goto v___jp_1526_;
}
}
else
{
lean_object* v_a_1826_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1826_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1826_);
lean_dec_ref_known(v___x_1764_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1826_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1827_; 
lean_dec(v_a_1716_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1827_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1734_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1827_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1828_; 
lean_dec(v_a_1716_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1828_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1726_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1828_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1829_; 
lean_dec(v_a_1716_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1829_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1829_);
lean_dec_ref_known(v___x_1718_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1829_;
goto v___jp_1526_;
}
}
else
{
lean_dec(v_a_1716_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = lean_box(0);
v___x_1831_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1830_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1831_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1833_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1832_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1834_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1835_;
goto v___jp_1536_;
}
else
{
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1833_;
goto v___jp_1536_;
}
}
}
}
else
{
lean_object* v_a_1836_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1836_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1715_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1836_;
goto v___jp_1526_;
}
}
else
{
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_box(0);
v___x_1838_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1837_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1838_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1840_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1510_, v___x_1839_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref_known(v___x_1840_, 1);
v___x_1842_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1841_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_);
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1842_;
goto v___jp_1536_;
}
else
{
v___y_1537_ = v_a_1575_;
v___y_1538_ = v___x_1711_;
v___y_1539_ = v___x_1840_;
goto v___jp_1536_;
}
}
}
}
else
{
lean_object* v_a_1843_; 
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1843_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1843_);
lean_dec_ref_known(v___x_1712_, 1);
v___y_1527_ = v_a_1575_;
v___y_1528_ = v___x_1711_;
v_a_1529_ = v_a_1843_;
goto v___jp_1526_;
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec_ref(v___f_1509_);
lean_dec(v_mvarId_1300_);
lean_dec(v_declName_1299_);
v_a_1844_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1574_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1574_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
v___jp_1306_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
return v___x_1308_;
}
v___jp_1309_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_box(0);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2069_, lean_object* v_as_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
if (lean_obj_tag(v_as_2070_) == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
lean_dec(v_declName_2069_);
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
return v___x_2077_;
}
else
{
lean_object* v_head_2078_; lean_object* v_tail_2079_; lean_object* v___x_2080_; 
v_head_2078_ = lean_ctor_get(v_as_2070_, 0);
lean_inc(v_head_2078_);
v_tail_2079_ = lean_ctor_get(v_as_2070_, 1);
lean_inc(v_tail_2079_);
lean_dec_ref_known(v_as_2070_, 2);
lean_inc(v_declName_2069_);
v___x_2080_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2069_, v_head_2078_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_dec_ref_known(v___x_2080_, 1);
v_as_2070_ = v_tail_2079_;
goto _start;
}
else
{
lean_dec(v_tail_2079_);
lean_dec(v_declName_2069_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2082_, lean_object* v_as_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2082_, v_as_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2090_, lean_object* v_as_2091_, lean_object* v_i_2092_, lean_object* v_stop_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
size_t v_i_boxed_2100_; size_t v_stop_boxed_2101_; lean_object* v_res_2102_; 
v_i_boxed_2100_ = lean_unbox_usize(v_i_2092_);
lean_dec(v_i_2092_);
v_stop_boxed_2101_ = lean_unbox_usize(v_stop_2093_);
lean_dec(v_stop_2093_);
v_res_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2090_, v_as_2091_, v_i_boxed_2100_, v_stop_boxed_2101_, v_b_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec_ref(v_as_2091_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2103_, lean_object* v___x_2104_, lean_object* v_declName_2105_, lean_object* v_____r_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2103_, v___x_2104_, v_declName_2105_, v_____r_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___x_2104_);
lean_dec_ref(v_val_2103_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2113_, lean_object* v_mvarId_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2113_, v_mvarId_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_00_u03b1_2121_, lean_object* v_x_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_2122_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2129_, lean_object* v_x_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_00_u03b1_2129_, v_x_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2137_, uint8_t v_skipRealize_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; lean_object* v_env_2142_; uint8_t v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2141_ = lean_st_ref_get(v___y_2139_);
v_env_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc_ref(v_env_2142_);
lean_dec(v___x_2141_);
v___x_2143_ = l_Lean_Environment_contains(v_env_2142_, v_constName_2137_, v_skipRealize_2138_);
v___x_2144_ = lean_box(v___x_2143_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2146_, lean_object* v_skipRealize_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
uint8_t v_skipRealize_boxed_2150_; lean_object* v_res_2151_; 
v_skipRealize_boxed_2150_ = lean_unbox(v_skipRealize_2147_);
v_res_2151_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2146_, v_skipRealize_boxed_2150_, v___y_2148_);
lean_dec(v___y_2148_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2152_, uint8_t v_skipRealize_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2152_, v_skipRealize_2153_, v___y_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2160_, lean_object* v_skipRealize_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
uint8_t v_skipRealize_boxed_2167_; lean_object* v_res_2168_; 
v_skipRealize_boxed_2167_ = lean_unbox(v_skipRealize_2161_);
v_res_2168_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2160_, v_skipRealize_boxed_2167_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2169_, lean_object* v___x_2170_, lean_object* v___x_2171_, lean_object* v_snd_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
lean_inc_ref(v_snd_2169_);
v___x_2178_ = l_Lean_Meta_mkCongrArg(v_snd_2169_, v___x_2170_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
v___x_2180_ = l_Lean_Expr_app___override(v_snd_2169_, v___x_2171_);
v___x_2181_ = l_Lean_MVarId_replaceTargetEq(v_snd_2172_, v___x_2180_, v_a_2179_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
return v___x_2181_;
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_snd_2172_);
lean_dec_ref(v___x_2171_);
lean_dec_ref(v_snd_2169_);
v_a_2182_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2178_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2178_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2190_, lean_object* v___x_2191_, lean_object* v___x_2192_, lean_object* v_snd_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2190_, v___x_2191_, v___x_2192_, v_snd_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2199_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2206_ = l_Lean_stringToMessageData(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2209_ = l_Lean_stringToMessageData(v___x_2208_);
return v___x_2209_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2212_ = l_Lean_stringToMessageData(v___x_2211_);
return v___x_2212_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2214_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2215_ = l_Lean_stringToMessageData(v___x_2214_);
return v___x_2215_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2218_ = l_Lean_stringToMessageData(v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2220_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2221_ = l_Lean_stringToMessageData(v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2222_, lean_object* v___x_2223_, lean_object* v_cls_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
lean_inc(v_mvarId_2222_);
v___x_2230_ = l_Lean_MVarId_getType(v_mvarId_2222_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2231_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v_fst_2234_; lean_object* v_snd_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2389_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v_fst_2234_ = lean_ctor_get(v_a_2233_, 0);
v_snd_2235_ = lean_ctor_get(v_a_2233_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v_a_2233_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2237_ = v_a_2233_;
v_isShared_2238_ = v_isSharedCheck_2389_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_snd_2235_);
lean_inc(v_fst_2234_);
lean_dec(v_a_2233_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2389_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; lean_object* v___x_2244_; lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2388_; 
v___x_2239_ = l_Lean_Expr_getAppFn(v_fst_2234_);
v___x_2240_ = l_Lean_Expr_constName_x21(v___x_2239_);
v___x_2241_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2242_ = l_Lean_Name_str___override(v___x_2240_, v___x_2241_);
v___x_2243_ = 1;
lean_inc(v___x_2242_);
v___x_2244_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2242_, v___x_2243_, v___y_2228_);
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2388_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2388_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v_nargs_2249_; lean_object* v___x_2250_; lean_object* v_dummy_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; uint8_t v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; uint8_t v___x_2371_; 
v_nargs_2249_ = l_Lean_Expr_getAppNumArgs(v_fst_2234_);
v___x_2250_ = l_Lean_Expr_constLevels_x21(v___x_2239_);
lean_dec_ref(v___x_2239_);
v_dummy_2251_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
lean_inc(v_nargs_2249_);
v___x_2252_ = lean_mk_array(v_nargs_2249_, v_dummy_2251_);
v___x_2253_ = lean_unsigned_to_nat(1u);
v___x_2254_ = lean_nat_sub(v_nargs_2249_, v___x_2253_);
lean_dec(v_nargs_2249_);
v___x_2255_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2234_, v___x_2252_, v___x_2254_);
v___x_2371_ = lean_unbox(v_a_2245_);
lean_dec(v_a_2245_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v___x_2255_);
lean_dec(v___x_2250_);
lean_del_object(v___x_2247_);
lean_del_object(v___x_2237_);
lean_dec(v_snd_2235_);
lean_dec(v_cls_2224_);
v___x_2372_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2373_ = l_Lean_MessageData_ofName(v___x_2242_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2372_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v_mvarId_2222_);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2378_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2379_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2379_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2379_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
else
{
v___y_2297_ = v___y_2225_;
v___y_2298_ = v___y_2226_;
v___y_2299_ = v___y_2227_;
v___y_2300_ = v___y_2228_;
goto v___jp_2296_;
}
v___jp_2256_:
{
lean_object* v___x_2265_; 
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
lean_inc_ref(v___y_2261_);
lean_inc_ref(v___y_2259_);
v___x_2265_ = lean_infer_type(v___y_2259_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2268_ = l_Lean_MVarId_define(v_mvarId_2222_, v___x_2267_, v_a_2266_, v___y_2259_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
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
v___x_2274_ = l_Lean_Expr_appFn_x21(v___y_2258_);
lean_dec_ref(v___y_2258_);
v___x_2275_ = l_Lean_mkFVar(v_fst_2272_);
v___x_2276_ = l_Lean_Expr_app___override(v___x_2274_, v___x_2275_);
v___x_2277_ = l_Lean_mkAppN(v___y_2257_, v___x_2255_);
lean_dec_ref(v___x_2255_);
v___f_2278_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2278_, 0, v_snd_2235_);
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
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2235_);
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
lean_dec_ref(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2235_);
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
lean_dec(v_snd_2235_);
lean_dec(v_mvarId_2222_);
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
lean_inc(v___x_2242_);
v___x_2301_ = l_Lean_mkConst(v___x_2242_, v___x_2250_);
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
lean_dec(v_snd_2235_);
lean_dec(v_cls_2224_);
v___x_2309_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2310_ = l_Lean_MessageData_ofName(v___x_2242_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set_tag(v___x_2237_, 7);
lean_ctor_set(v___x_2237_, 1, v___x_2310_);
lean_ctor_set(v___x_2237_, 0, v___x_2309_);
v___x_2312_ = v___x_2237_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2313_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set_tag(v___x_2247_, 1);
lean_ctor_set(v___x_2247_, 0, v_mvarId_2222_);
v___x_2316_ = v___x_2247_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_mvarId_2222_);
v___x_2316_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2317_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
return v___x_2318_;
}
}
}
else
{
lean_object* v_toCold_2321_; lean_object* v_options_2322_; lean_object* v_inheritedTraceOptions_2323_; uint8_t v_hasTrace_2324_; lean_object* v___x_2325_; lean_object* v_nargs_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_del_object(v___x_2247_);
lean_dec(v___x_2242_);
v_toCold_2321_ = lean_ctor_get(v___y_2299_, 0);
v_options_2322_ = lean_ctor_get(v_toCold_2321_, 2);
v_inheritedTraceOptions_2323_ = lean_ctor_get(v_toCold_2321_, 11);
v_hasTrace_2324_ = lean_ctor_get_uint8(v_options_2322_, sizeof(void*)*1);
v___x_2325_ = l_Lean_Expr_appArg_x21(v_a_2305_);
lean_dec(v_a_2305_);
v_nargs_2326_ = l_Lean_Expr_getAppNumArgs(v___x_2325_);
lean_inc(v_nargs_2326_);
v___x_2327_ = lean_mk_array(v_nargs_2326_, v_dummy_2251_);
v___x_2328_ = lean_nat_sub(v_nargs_2326_, v___x_2253_);
lean_dec(v_nargs_2326_);
lean_inc_ref(v___x_2325_);
v___x_2329_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2325_, v___x_2327_, v___x_2328_);
v___x_2330_ = lean_array_get_size(v___x_2329_);
v___x_2331_ = lean_nat_sub(v___x_2330_, v___x_2253_);
v___x_2332_ = lean_array_get(v___x_2223_, v___x_2329_, v___x_2331_);
lean_dec(v___x_2331_);
lean_dec_ref(v___x_2329_);
if (v_hasTrace_2324_ == 0)
{
lean_del_object(v___x_2237_);
lean_dec(v_cls_2224_);
v___y_2257_ = v___x_2301_;
v___y_2258_ = v___x_2325_;
v___y_2259_ = v___x_2332_;
v___y_2260_ = v___x_2308_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2224_);
v___x_2334_ = l_Lean_Name_append(v___x_2333_, v_cls_2224_);
v___x_2335_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2323_, v_options_2322_, v___x_2334_);
lean_dec(v___x_2334_);
if (v___x_2335_ == 0)
{
lean_del_object(v___x_2237_);
lean_dec(v_cls_2224_);
v___y_2257_ = v___x_2301_;
v___y_2258_ = v___x_2325_;
v___y_2259_ = v___x_2332_;
v___y_2260_ = v___x_2308_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2336_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2337_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2332_);
v___x_2338_ = l_Lean_inlineExpr(v___x_2332_, v___x_2337_);
if (v_isShared_2238_ == 0)
{
lean_ctor_set_tag(v___x_2237_, 7);
lean_ctor_set(v___x_2237_, 1, v___x_2338_);
lean_ctor_set(v___x_2237_, 0, v___x_2336_);
v___x_2340_ = v___x_2237_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2341_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2340_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
lean_inc_ref(v___x_2325_);
v___x_2343_ = l_Lean_indentExpr(v___x_2325_);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2224_, v___x_2344_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_dec_ref_known(v___x_2345_, 1);
v___y_2257_ = v___x_2301_;
v___y_2258_ = v___x_2325_;
v___y_2259_ = v___x_2332_;
v___y_2260_ = v___x_2308_;
v___y_2261_ = v___y_2297_;
v___y_2262_ = v___y_2298_;
v___y_2263_ = v___y_2299_;
v___y_2264_ = v___y_2300_;
goto v___jp_2256_;
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec(v___x_2332_);
lean_dec_ref(v___x_2325_);
lean_dec_ref(v___x_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v___x_2255_);
lean_dec(v_snd_2235_);
lean_dec(v_mvarId_2222_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
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
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v___x_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v___x_2255_);
lean_del_object(v___x_2247_);
lean_dec(v___x_2242_);
lean_del_object(v___x_2237_);
lean_dec(v_snd_2235_);
lean_dec(v_cls_2224_);
lean_dec(v_mvarId_2222_);
v_a_2355_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2304_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2304_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v___x_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v___x_2255_);
lean_del_object(v___x_2247_);
lean_dec(v___x_2242_);
lean_del_object(v___x_2237_);
lean_dec(v_snd_2235_);
lean_dec(v_cls_2224_);
lean_dec(v_mvarId_2222_);
v_a_2363_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2302_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2302_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v_cls_2224_);
lean_dec(v_mvarId_2222_);
v_a_2390_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2232_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2232_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec(v_cls_2224_);
lean_dec(v_mvarId_2222_);
v_a_2398_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2230_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2230_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2406_, lean_object* v___x_2407_, lean_object* v_cls_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2406_, v___x_2407_, v_cls_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec_ref(v___x_2407_);
return v_res_2414_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2417_ = l_Lean_stringToMessageData(v___x_2416_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2418_, lean_object* v_x_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_mvarId_2418_);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___x_2425_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2429_, lean_object* v_x_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2429_, v_x_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec_ref(v_x_2430_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2437_, lean_object* v_mvarId_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_toCold_2444_; lean_object* v_options_2445_; lean_object* v_inheritedTraceOptions_2446_; uint8_t v_hasTrace_2447_; lean_object* v___x_2448_; lean_object* v_cls_2449_; lean_object* v___f_2450_; 
v_toCold_2444_ = lean_ctor_get(v_a_2441_, 0);
v_options_2445_ = lean_ctor_get(v_toCold_2444_, 2);
v_inheritedTraceOptions_2446_ = lean_ctor_get(v_toCold_2444_, 11);
v_hasTrace_2447_ = lean_ctor_get_uint8(v_options_2445_, sizeof(void*)*1);
v___x_2448_ = l_Lean_instInhabitedExpr;
v_cls_2449_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2438_);
v___f_2450_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2450_, 0, v_mvarId_2438_);
lean_closure_set(v___f_2450_, 1, v___x_2448_);
lean_closure_set(v___f_2450_, 2, v_cls_2449_);
if (v_hasTrace_2447_ == 0)
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2438_, v___f_2450_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2453_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2453_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2437_, v_a_2452_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2453_;
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_declName_2437_);
v_a_2454_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2451_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2451_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v_a_2469_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v_a_2484_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v_a_2489_; lean_object* v___y_2499_; lean_object* v___y_2500_; lean_object* v_a_2501_; 
lean_inc(v_mvarId_2438_);
v___f_2462_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2462_, 0, v_mvarId_2438_);
v___x_2463_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2464_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2465_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2446_, v_options_2445_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = l_Lean_trace_profiler;
v___x_2537_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2445_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; 
lean_dec_ref(v___f_2462_);
v___x_2538_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2438_, v___f_2450_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2540_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2437_, v_a_2539_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2540_;
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_declName_2437_);
v_a_2541_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2538_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2538_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
goto v___jp_2503_;
}
}
else
{
goto v___jp_2503_;
}
v___jp_2466_:
{
lean_object* v___x_2470_; double v___x_2471_; double v___x_2472_; double v___x_2473_; double v___x_2474_; double v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2470_ = lean_io_mono_nanos_now();
v___x_2471_ = lean_float_of_nat(v___y_2467_);
v___x_2472_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2473_ = lean_float_div(v___x_2471_, v___x_2472_);
v___x_2474_ = lean_float_of_nat(v___x_2470_);
v___x_2475_ = lean_float_div(v___x_2474_, v___x_2472_);
v___x_2476_ = lean_box_float(v___x_2473_);
v___x_2477_ = lean_box_float(v___x_2475_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v_a_2469_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2449_, v_hasTrace_2447_, v___x_2463_, v_options_2445_, v___x_2465_, v___y_2468_, v___f_2462_, v___x_2479_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2480_;
}
v___jp_2481_:
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2485_, 0, v_a_2484_);
v___y_2467_ = v___y_2482_;
v___y_2468_ = v___y_2483_;
v_a_2469_ = v___x_2485_;
goto v___jp_2466_;
}
v___jp_2486_:
{
lean_object* v___x_2490_; double v___x_2491_; double v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2490_ = lean_io_get_num_heartbeats();
v___x_2491_ = lean_float_of_nat(v___y_2487_);
v___x_2492_ = lean_float_of_nat(v___x_2490_);
v___x_2493_ = lean_box_float(v___x_2491_);
v___x_2494_ = lean_box_float(v___x_2492_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2489_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2449_, v_hasTrace_2447_, v___x_2463_, v_options_2445_, v___x_2465_, v___y_2488_, v___f_2462_, v___x_2496_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
return v___x_2497_;
}
v___jp_2498_:
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_a_2501_);
v___y_2487_ = v___y_2499_;
v___y_2488_ = v___y_2500_;
v_a_2489_ = v___x_2502_;
goto v___jp_2486_;
}
v___jp_2503_:
{
lean_object* v___x_2504_; lean_object* v_a_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___x_2504_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2442_);
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref(v___x_2504_);
v___x_2506_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2507_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2445_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_io_mono_nanos_now();
v___x_2509_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2438_, v___f_2450_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___x_2511_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2509_, 1);
v___x_2511_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2437_, v_a_2510_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set_tag(v___x_2514_, 1);
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
v___y_2467_ = v___x_2508_;
v___y_2468_ = v_a_2505_;
v_a_2469_ = v___x_2517_;
goto v___jp_2466_;
}
}
}
else
{
lean_object* v_a_2520_; 
v_a_2520_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v___x_2511_, 1);
v___y_2482_ = v___x_2508_;
v___y_2483_ = v_a_2505_;
v_a_2484_ = v_a_2520_;
goto v___jp_2481_;
}
}
else
{
lean_object* v_a_2521_; 
lean_dec(v_declName_2437_);
v_a_2521_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2509_, 1);
v___y_2482_ = v___x_2508_;
v___y_2483_ = v_a_2505_;
v_a_2484_ = v_a_2521_;
goto v___jp_2481_;
}
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_io_get_num_heartbeats();
v___x_2523_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2438_, v___f_2450_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; 
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2525_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2437_, v_a_2524_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
lean_ctor_set_tag(v___x_2528_, 1);
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
v___y_2487_ = v___x_2522_;
v___y_2488_ = v_a_2505_;
v_a_2489_ = v___x_2531_;
goto v___jp_2486_;
}
}
}
else
{
lean_object* v_a_2534_; 
v_a_2534_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2525_, 1);
v___y_2499_ = v___x_2522_;
v___y_2500_ = v_a_2505_;
v_a_2501_ = v_a_2534_;
goto v___jp_2498_;
}
}
else
{
lean_object* v_a_2535_; 
lean_dec(v_declName_2437_);
v_a_2535_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2523_, 1);
v___y_2499_ = v___x_2522_;
v___y_2500_ = v_a_2505_;
v_a_2501_ = v_a_2535_;
goto v___jp_2498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2549_, lean_object* v_mvarId_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2549_, v_mvarId_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2557_, lean_object* v___y_2558_){
_start:
{
uint8_t v___x_2560_; 
v___x_2560_ = l_Lean_Expr_hasMVar(v_e_2557_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2561_, 0, v_e_2557_);
return v___x_2561_;
}
else
{
lean_object* v___x_2562_; lean_object* v_mctx_2563_; lean_object* v___x_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2567_; lean_object* v_cache_2568_; lean_object* v_zetaDeltaFVarIds_2569_; lean_object* v_postponed_2570_; lean_object* v_diag_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2580_; 
v___x_2562_ = lean_st_ref_get(v___y_2558_);
v_mctx_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc_ref(v_mctx_2563_);
lean_dec(v___x_2562_);
v___x_2564_ = l_Lean_instantiateMVarsCore(v_mctx_2563_, v_e_2557_);
v_fst_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_fst_2565_);
v_snd_2566_ = lean_ctor_get(v___x_2564_, 1);
lean_inc(v_snd_2566_);
lean_dec_ref(v___x_2564_);
v___x_2567_ = lean_st_ref_take(v___y_2558_);
v_cache_2568_ = lean_ctor_get(v___x_2567_, 1);
v_zetaDeltaFVarIds_2569_ = lean_ctor_get(v___x_2567_, 2);
v_postponed_2570_ = lean_ctor_get(v___x_2567_, 3);
v_diag_2571_ = lean_ctor_get(v___x_2567_, 4);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2580_ == 0)
{
lean_object* v_unused_2581_; 
v_unused_2581_ = lean_ctor_get(v___x_2567_, 0);
lean_dec(v_unused_2581_);
v___x_2573_ = v___x_2567_;
v_isShared_2574_ = v_isSharedCheck_2580_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_diag_2571_);
lean_inc(v_postponed_2570_);
lean_inc(v_zetaDeltaFVarIds_2569_);
lean_inc(v_cache_2568_);
lean_dec(v___x_2567_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2580_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v_snd_2566_);
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_snd_2566_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v_cache_2568_);
lean_ctor_set(v_reuseFailAlloc_2579_, 2, v_zetaDeltaFVarIds_2569_);
lean_ctor_set(v_reuseFailAlloc_2579_, 3, v_postponed_2570_);
lean_ctor_set(v_reuseFailAlloc_2579_, 4, v_diag_2571_);
v___x_2576_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_st_ref_put(v___y_2558_, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_fst_2565_);
return v___x_2578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2582_, v___y_2583_);
lean_dec(v___y_2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2586_, v___y_2588_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2600_, uint8_t v_allowLevelAssignments_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2601_, v_k_2600_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
v_a_2616_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2607_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2607_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2624_, lean_object* v_allowLevelAssignments_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2631_; lean_object* v_res_2632_; 
v_allowLevelAssignments_boxed_2631_ = lean_unbox(v_allowLevelAssignments_2625_);
v_res_2632_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2624_, v_allowLevelAssignments_boxed_2631_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2633_, lean_object* v_k_2634_, uint8_t v_allowLevelAssignments_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2634_, v_allowLevelAssignments_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_k_2643_, lean_object* v_allowLevelAssignments_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2650_; lean_object* v_res_2651_; 
v_allowLevelAssignments_boxed_2650_ = lean_unbox(v_allowLevelAssignments_2644_);
v_res_2651_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2642_, v_k_2643_, v_allowLevelAssignments_boxed_2650_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2652_, lean_object* v_e_2653_){
_start:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = l_Lean_indentD(v_e_2653_);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2652_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2656_, lean_object* v___x_2657_, lean_object* v_declName_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2656_, v___x_2657_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = l_Lean_Expr_mvarId_x21(v_a_2665_);
v___x_2667_ = l_Lean_MVarId_intros(v___x_2666_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v_snd_2669_; lean_object* v___x_2670_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2667_, 1);
v_snd_2669_ = lean_ctor_get(v_a_2668_, 1);
lean_inc_n(v_snd_2669_, 2);
lean_dec(v_a_2668_);
v___x_2670_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2669_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; uint8_t v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_unbox(v_a_2671_);
lean_dec(v_a_2671_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2669_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2658_, v_a_2674_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2676_; 
lean_dec_ref_known(v___x_2675_, 1);
v___x_2676_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2665_, v___y_2660_);
return v___x_2676_;
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_dec(v_a_2665_);
v_a_2677_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2675_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2675_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_a_2665_);
lean_dec(v_declName_2658_);
v_a_2685_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2673_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2673_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v___x_2693_; 
lean_dec(v_snd_2669_);
lean_dec(v_declName_2658_);
v___x_2693_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2665_, v___y_2660_);
return v___x_2693_;
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_snd_2669_);
lean_dec(v_a_2665_);
lean_dec(v_declName_2658_);
v_a_2694_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2670_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2670_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec(v_a_2665_);
lean_dec(v_declName_2658_);
v_a_2702_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2667_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2667_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
else
{
lean_dec(v_declName_2658_);
return v___x_2664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2710_, lean_object* v___x_2711_, lean_object* v_declName_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2710_, v___x_2711_, v_declName_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2718_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2721_ = l_Lean_stringToMessageData(v___x_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2729_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2730_ = l_Lean_indentExpr(v_type_2722_);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2733_, v_x_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec_ref(v_x_2734_);
return v_res_2740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2741_){
_start:
{
if (lean_obj_tag(v_e_2741_) == 0)
{
uint8_t v___x_2742_; 
v___x_2742_ = 2;
return v___x_2742_;
}
else
{
lean_object* v_a_2743_; uint8_t v___x_2744_; 
v_a_2743_ = lean_ctor_get(v_e_2741_, 0);
v___x_2744_ = l_Lean_Expr_hasSyntheticSorry(v_a_2743_);
if (v___x_2744_ == 0)
{
uint8_t v___x_2745_; 
v___x_2745_ = 0;
return v___x_2745_;
}
else
{
uint8_t v___x_2746_; 
v___x_2746_ = 1;
return v___x_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2747_){
_start:
{
uint8_t v_res_2748_; lean_object* v_r_2749_; 
v_res_2748_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2747_);
lean_dec_ref(v_e_2747_);
v_r_2749_ = lean_box(v_res_2748_);
return v_r_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2750_, uint8_t v_collapsed_2751_, lean_object* v_tag_2752_, lean_object* v_opts_2753_, uint8_t v_clsEnabled_2754_, lean_object* v_oldTraces_2755_, lean_object* v_msg_2756_, lean_object* v_resStartStop_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_fst_2763_; lean_object* v_snd_2764_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v_data_2768_; lean_object* v_fst_2779_; lean_object* v_snd_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; lean_object* v___y_2784_; lean_object* v_a_2785_; uint8_t v___y_2800_; double v___y_2831_; 
v_fst_2763_ = lean_ctor_get(v_resStartStop_2757_, 0);
lean_inc(v_fst_2763_);
v_snd_2764_ = lean_ctor_get(v_resStartStop_2757_, 1);
lean_inc(v_snd_2764_);
lean_dec_ref(v_resStartStop_2757_);
v_fst_2779_ = lean_ctor_get(v_snd_2764_, 0);
lean_inc(v_fst_2779_);
v_snd_2780_ = lean_ctor_get(v_snd_2764_, 1);
lean_inc(v_snd_2780_);
lean_dec(v_snd_2764_);
v___x_2781_ = l_Lean_trace_profiler;
v___x_2782_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2753_, v___x_2781_);
if (v___x_2782_ == 0)
{
v___y_2800_ = v___x_2782_;
goto v___jp_2799_;
}
else
{
lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2837_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2753_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; lean_object* v___x_2839_; double v___x_2840_; double v___x_2841_; double v___x_2842_; 
v___x_2838_ = l_Lean_trace_profiler_threshold;
v___x_2839_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2753_, v___x_2838_);
v___x_2840_ = lean_float_of_nat(v___x_2839_);
v___x_2841_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_2842_ = lean_float_div(v___x_2840_, v___x_2841_);
v___y_2831_ = v___x_2842_;
goto v___jp_2830_;
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; double v___x_2845_; 
v___x_2843_ = l_Lean_trace_profiler_threshold;
v___x_2844_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2753_, v___x_2843_);
v___x_2845_ = lean_float_of_nat(v___x_2844_);
v___y_2831_ = v___x_2845_;
goto v___jp_2830_;
}
}
v___jp_2765_:
{
lean_object* v___x_2769_; 
lean_inc(v___y_2767_);
v___x_2769_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_2755_, v_data_2768_, v___y_2767_, v___y_2766_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v___x_2770_; 
lean_dec_ref_known(v___x_2769_, 1);
v___x_2770_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2763_);
return v___x_2770_;
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v_fst_2763_);
v_a_2771_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2769_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2769_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
v___jp_2783_:
{
uint8_t v_result_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; double v___x_2789_; lean_object* v_data_2790_; 
v_result_2786_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2763_);
v___x_2787_ = lean_box(v_result_2786_);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
v___x_2789_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2752_);
lean_inc_ref(v___x_2788_);
lean_inc(v_cls_2750_);
v_data_2790_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2790_, 0, v_cls_2750_);
lean_ctor_set(v_data_2790_, 1, v___x_2788_);
lean_ctor_set(v_data_2790_, 2, v_tag_2752_);
lean_ctor_set_float(v_data_2790_, sizeof(void*)*3, v___x_2789_);
lean_ctor_set_float(v_data_2790_, sizeof(void*)*3 + 8, v___x_2789_);
lean_ctor_set_uint8(v_data_2790_, sizeof(void*)*3 + 16, v_collapsed_2751_);
if (v___x_2782_ == 0)
{
lean_dec_ref_known(v___x_2788_, 1);
lean_dec(v_snd_2780_);
lean_dec(v_fst_2779_);
lean_dec_ref(v_tag_2752_);
lean_dec(v_cls_2750_);
v___y_2766_ = v_a_2785_;
v___y_2767_ = v___y_2784_;
v_data_2768_ = v_data_2790_;
goto v___jp_2765_;
}
else
{
lean_object* v_data_2791_; double v___x_2792_; double v___x_2793_; 
lean_dec_ref_known(v_data_2790_, 3);
v_data_2791_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2791_, 0, v_cls_2750_);
lean_ctor_set(v_data_2791_, 1, v___x_2788_);
lean_ctor_set(v_data_2791_, 2, v_tag_2752_);
v___x_2792_ = lean_unbox_float(v_fst_2779_);
lean_dec(v_fst_2779_);
lean_ctor_set_float(v_data_2791_, sizeof(void*)*3, v___x_2792_);
v___x_2793_ = lean_unbox_float(v_snd_2780_);
lean_dec(v_snd_2780_);
lean_ctor_set_float(v_data_2791_, sizeof(void*)*3 + 8, v___x_2793_);
lean_ctor_set_uint8(v_data_2791_, sizeof(void*)*3 + 16, v_collapsed_2751_);
v___y_2766_ = v_a_2785_;
v___y_2767_ = v___y_2784_;
v_data_2768_ = v_data_2791_;
goto v___jp_2765_;
}
}
v___jp_2794_:
{
lean_object* v_ref_2795_; lean_object* v___x_2796_; 
v_ref_2795_ = lean_ctor_get(v___y_2760_, 2);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v_fst_2763_);
v___x_2796_ = lean_apply_6(v_msg_2756_, v_fst_2763_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, lean_box(0));
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___y_2784_ = v_ref_2795_;
v_a_2785_ = v_a_2797_;
goto v___jp_2783_;
}
else
{
lean_object* v___x_2798_; 
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_2784_ = v_ref_2795_;
v_a_2785_ = v___x_2798_;
goto v___jp_2783_;
}
}
v___jp_2799_:
{
if (v_clsEnabled_2754_ == 0)
{
if (v___y_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v_traceState_2802_; lean_object* v_env_2803_; lean_object* v_nextMacroScope_2804_; lean_object* v_ngen_2805_; lean_object* v_auxDeclNGen_2806_; lean_object* v_cache_2807_; lean_object* v_messages_2808_; lean_object* v_infoState_2809_; lean_object* v_snapshotTasks_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_snd_2780_);
lean_dec(v_fst_2779_);
lean_dec_ref(v_msg_2756_);
lean_dec_ref(v_tag_2752_);
lean_dec(v_cls_2750_);
v___x_2801_ = lean_st_ref_take(v___y_2761_);
v_traceState_2802_ = lean_ctor_get(v___x_2801_, 4);
v_env_2803_ = lean_ctor_get(v___x_2801_, 0);
v_nextMacroScope_2804_ = lean_ctor_get(v___x_2801_, 1);
v_ngen_2805_ = lean_ctor_get(v___x_2801_, 2);
v_auxDeclNGen_2806_ = lean_ctor_get(v___x_2801_, 3);
v_cache_2807_ = lean_ctor_get(v___x_2801_, 5);
v_messages_2808_ = lean_ctor_get(v___x_2801_, 6);
v_infoState_2809_ = lean_ctor_get(v___x_2801_, 7);
v_snapshotTasks_2810_ = lean_ctor_get(v___x_2801_, 8);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2812_ = v___x_2801_;
v_isShared_2813_ = v_isSharedCheck_2829_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_snapshotTasks_2810_);
lean_inc(v_infoState_2809_);
lean_inc(v_messages_2808_);
lean_inc(v_cache_2807_);
lean_inc(v_traceState_2802_);
lean_inc(v_auxDeclNGen_2806_);
lean_inc(v_ngen_2805_);
lean_inc(v_nextMacroScope_2804_);
lean_inc(v_env_2803_);
lean_dec(v___x_2801_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2829_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
uint64_t v_tid_2814_; lean_object* v_traces_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2828_; 
v_tid_2814_ = lean_ctor_get_uint64(v_traceState_2802_, sizeof(void*)*1);
v_traces_2815_ = lean_ctor_get(v_traceState_2802_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_traceState_2802_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2817_ = v_traceState_2802_;
v_isShared_2818_ = v_isSharedCheck_2828_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_traces_2815_);
lean_dec(v_traceState_2802_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2828_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2755_, v_traces_2815_);
lean_dec_ref(v_traces_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2819_);
lean_ctor_set_uint64(v_reuseFailAlloc_2827_, sizeof(void*)*1, v_tid_2814_);
v___x_2821_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 4, v___x_2821_);
v___x_2823_ = v___x_2812_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_env_2803_);
lean_ctor_set(v_reuseFailAlloc_2826_, 1, v_nextMacroScope_2804_);
lean_ctor_set(v_reuseFailAlloc_2826_, 2, v_ngen_2805_);
lean_ctor_set(v_reuseFailAlloc_2826_, 3, v_auxDeclNGen_2806_);
lean_ctor_set(v_reuseFailAlloc_2826_, 4, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2826_, 5, v_cache_2807_);
lean_ctor_set(v_reuseFailAlloc_2826_, 6, v_messages_2808_);
lean_ctor_set(v_reuseFailAlloc_2826_, 7, v_infoState_2809_);
lean_ctor_set(v_reuseFailAlloc_2826_, 8, v_snapshotTasks_2810_);
v___x_2823_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = lean_st_ref_put(v___y_2761_, v___x_2823_);
v___x_2825_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2763_);
return v___x_2825_;
}
}
}
}
}
else
{
goto v___jp_2794_;
}
}
else
{
goto v___jp_2794_;
}
}
v___jp_2830_:
{
double v___x_2832_; double v___x_2833_; double v___x_2834_; uint8_t v___x_2835_; 
v___x_2832_ = lean_unbox_float(v_snd_2780_);
v___x_2833_ = lean_unbox_float(v_fst_2779_);
v___x_2834_ = lean_float_sub(v___x_2832_, v___x_2833_);
v___x_2835_ = lean_float_decLt(v___y_2831_, v___x_2834_);
v___y_2800_ = v___x_2835_;
goto v___jp_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2846_, lean_object* v_collapsed_2847_, lean_object* v_tag_2848_, lean_object* v_opts_2849_, lean_object* v_clsEnabled_2850_, lean_object* v_oldTraces_2851_, lean_object* v_msg_2852_, lean_object* v_resStartStop_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
uint8_t v_collapsed_boxed_2859_; uint8_t v_clsEnabled_boxed_2860_; lean_object* v_res_2861_; 
v_collapsed_boxed_2859_ = lean_unbox(v_collapsed_2847_);
v_clsEnabled_boxed_2860_ = lean_unbox(v_clsEnabled_2850_);
v_res_2861_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2846_, v_collapsed_boxed_2859_, v_tag_2848_, v_opts_2849_, v_clsEnabled_boxed_2860_, v_oldTraces_2851_, v_msg_2852_, v_resStartStop_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec_ref(v_opts_2849_);
return v_res_2861_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2864_ = l_Lean_stringToMessageData(v___x_2863_);
return v___x_2864_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2867_ = l_Lean_stringToMessageData(v___x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2868_, lean_object* v_type_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_toCold_2875_; lean_object* v_options_2876_; lean_object* v_inheritedTraceOptions_2877_; uint8_t v_hasTrace_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; lean_object* v___f_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_toCold_2875_ = lean_ctor_get(v_a_2872_, 0);
v_options_2876_ = lean_ctor_get(v_toCold_2875_, 2);
v_inheritedTraceOptions_2877_ = lean_ctor_get(v_toCold_2875_, 11);
v_hasTrace_2878_ = lean_ctor_get_uint8(v_options_2876_, sizeof(void*)*1);
v___x_2879_ = 0;
lean_inc(v_declName_2868_);
v___x_2880_ = l_Lean_MessageData_ofConstName(v_declName_2868_, v___x_2879_);
v___x_2881_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v___x_2880_);
v___x_2883_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___f_2885_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_2885_, 0, v___x_2884_);
v___x_2886_ = lean_box(0);
lean_inc_ref(v_type_2869_);
v___f_2887_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2887_, 0, v_type_2869_);
lean_closure_set(v___f_2887_, 1, v___x_2886_);
lean_closure_set(v___f_2887_, 2, v_declName_2868_);
v___x_2888_ = lean_box(v___x_2879_);
v___x_2889_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2889_, 0, lean_box(0));
lean_closure_set(v___x_2889_, 1, v___f_2887_);
lean_closure_set(v___x_2889_, 2, v___x_2888_);
if (v_hasTrace_2878_ == 0)
{
lean_object* v___x_2890_; 
lean_dec_ref(v_type_2869_);
v___x_2890_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2889_, v___f_2885_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2890_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2890_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
v_a_2899_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2890_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2890_);
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
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___f_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v_a_2915_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v_a_2930_; 
v___f_2907_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2907_, 0, v_type_2869_);
v___x_2908_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_2909_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2910_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2911_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2877_, v_options_2876_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2980_; uint8_t v___x_2981_; 
v___x_2980_ = l_Lean_trace_profiler;
v___x_2981_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2876_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; 
lean_dec_ref(v___f_2907_);
v___x_2982_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2889_, v___f_2885_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
v_a_2991_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2982_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2982_);
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
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
goto v___jp_2939_;
}
}
else
{
goto v___jp_2939_;
}
v___jp_2912_:
{
lean_object* v___x_2916_; double v___x_2917_; double v___x_2918_; double v___x_2919_; double v___x_2920_; double v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2916_ = lean_io_mono_nanos_now();
v___x_2917_ = lean_float_of_nat(v___y_2913_);
v___x_2918_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2919_ = lean_float_div(v___x_2917_, v___x_2918_);
v___x_2920_ = lean_float_of_nat(v___x_2916_);
v___x_2921_ = lean_float_div(v___x_2920_, v___x_2918_);
v___x_2922_ = lean_box_float(v___x_2919_);
v___x_2923_ = lean_box_float(v___x_2921_);
v___x_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2922_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_a_2915_);
lean_ctor_set(v___x_2925_, 1, v___x_2924_);
v___x_2926_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2908_, v_hasTrace_2878_, v___x_2909_, v_options_2876_, v___x_2911_, v___y_2914_, v___f_2907_, v___x_2925_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2926_;
}
v___jp_2927_:
{
lean_object* v___x_2931_; double v___x_2932_; double v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2931_ = lean_io_get_num_heartbeats();
v___x_2932_ = lean_float_of_nat(v___y_2928_);
v___x_2933_ = lean_float_of_nat(v___x_2931_);
v___x_2934_ = lean_box_float(v___x_2932_);
v___x_2935_ = lean_box_float(v___x_2933_);
v___x_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2934_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v_a_2930_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2908_, v_hasTrace_2878_, v___x_2909_, v_options_2876_, v___x_2911_, v___y_2929_, v___f_2907_, v___x_2937_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
return v___x_2938_;
}
v___jp_2939_:
{
lean_object* v___x_2940_; lean_object* v_a_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2940_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2873_);
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2943_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2876_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_io_mono_nanos_now();
v___x_2945_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2889_, v___f_2885_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
lean_ctor_set_tag(v___x_2948_, 1);
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
v___y_2913_ = v___x_2944_;
v___y_2914_ = v_a_2941_;
v_a_2915_ = v___x_2951_;
goto v___jp_2912_;
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
v_a_2954_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2945_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2945_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set_tag(v___x_2956_, 0);
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
v___y_2913_ = v___x_2944_;
v___y_2914_ = v_a_2941_;
v_a_2915_ = v___x_2959_;
goto v___jp_2912_;
}
}
}
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_io_get_num_heartbeats();
v___x_2963_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2889_, v___f_2885_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
lean_ctor_set_tag(v___x_2966_, 1);
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
v___y_2928_ = v___x_2962_;
v___y_2929_ = v_a_2941_;
v_a_2930_ = v___x_2969_;
goto v___jp_2927_;
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_a_2972_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2963_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2963_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
lean_ctor_set_tag(v___x_2974_, 0);
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
v___y_2928_ = v___x_2962_;
v___y_2929_ = v_a_2941_;
v_a_2930_ = v___x_2977_;
goto v___jp_2927_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_2999_, lean_object* v_type_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_2999_, v_type_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
return v_res_3006_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_3007_, lean_object* v_n_3008_, lean_object* v_x_3009_){
_start:
{
uint8_t v___x_3010_; 
v___x_3010_ = l_Lean_Environment_hasExposedBody(v_env_3007_, v_n_3008_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_env_3011_, lean_object* v_n_3012_, lean_object* v_x_3013_){
_start:
{
uint8_t v_res_3014_; lean_object* v_r_3015_; 
v_res_3014_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(v_env_3011_, v_n_3012_, v_x_3013_);
lean_dec_ref(v_x_3013_);
v_r_3015_ = lean_box(v_res_3014_);
return v_r_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3016_, lean_object* v_x_3017_){
_start:
{
if (lean_obj_tag(v_x_3017_) == 0)
{
lean_object* v_k_3018_; lean_object* v_v_3019_; lean_object* v_l_3020_; lean_object* v_r_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v_k_3018_ = lean_ctor_get(v_x_3017_, 1);
v_v_3019_ = lean_ctor_get(v_x_3017_, 2);
v_l_3020_ = lean_ctor_get(v_x_3017_, 3);
v_r_3021_ = lean_ctor_get(v_x_3017_, 4);
v___x_3022_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3016_, v_l_3020_);
lean_inc(v_v_3019_);
lean_inc(v_k_3018_);
v___x_3023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3023_, 0, v_k_3018_);
lean_ctor_set(v___x_3023_, 1, v_v_3019_);
v___x_3024_ = lean_array_push(v___x_3022_, v___x_3023_);
v_init_3016_ = v___x_3024_;
v_x_3017_ = v_r_3021_;
goto _start;
}
else
{
return v_init_3016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3026_, lean_object* v_x_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3026_, v_x_3027_);
lean_dec(v_x_3027_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_3031_, lean_object* v_s_3032_){
_start:
{
lean_object* v___f_3033_; lean_object* v___x_3034_; lean_object* v_all_3035_; lean_object* v___x_3036_; lean_object* v_exported_3037_; lean_object* v___x_3038_; 
v___f_3033_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3033_, 0, v_env_3031_);
v___x_3034_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v_all_3035_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3034_, v_s_3032_);
v___x_3036_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3033_, v_s_3032_);
v_exported_3037_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3034_, v___x_3036_);
lean_dec(v___x_3036_);
lean_inc_ref(v_exported_3037_);
v___x_3038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3038_, 0, v_exported_3037_);
lean_ctor_set(v___x_3038_, 1, v_exported_3037_);
lean_ctor_set(v___x_3038_, 2, v_all_3035_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___f_3051_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3052_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3053_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3054_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3052_, v___x_3053_, v___f_3051_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_a_3055_){
_start:
{
lean_object* v_res_3056_; 
v_res_3056_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_();
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(lean_object* v_init_3057_, lean_object* v_t_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3057_, v_t_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3060_, lean_object* v_t_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(v_init_3060_, v_t_3061_);
lean_dec(v_t_3061_);
return v_res_3062_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3063_; 
v___x_3063_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3063_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3068_, lean_object* v_declNames_3069_, lean_object* v_recArgPos_3070_, lean_object* v_fixedParamPerms_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v_levelParams_3075_; lean_object* v_declName_3076_; lean_object* v_type_3077_; lean_object* v_value_3078_; lean_object* v___x_3079_; 
v_levelParams_3075_ = lean_ctor_get(v_preDef_3068_, 1);
lean_inc(v_levelParams_3075_);
v_declName_3076_ = lean_ctor_get(v_preDef_3068_, 3);
lean_inc_n(v_declName_3076_, 2);
v_type_3077_ = lean_ctor_get(v_preDef_3068_, 6);
lean_inc_ref(v_type_3077_);
v_value_3078_ = lean_ctor_get(v_preDef_3068_, 7);
lean_inc_ref(v_value_3078_);
lean_dec_ref(v_preDef_3068_);
v___x_3079_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3076_, v_a_3072_, v_a_3073_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3109_; 
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v___x_3079_, 0);
lean_dec(v_unused_3110_);
v___x_3081_ = v___x_3079_;
v_isShared_3082_ = v_isSharedCheck_3109_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v___x_3079_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3109_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3083_; lean_object* v_env_3084_; lean_object* v_nextMacroScope_3085_; lean_object* v_ngen_3086_; lean_object* v_auxDeclNGen_3087_; lean_object* v_traceState_3088_; lean_object* v_messages_3089_; lean_object* v_infoState_3090_; lean_object* v_snapshotTasks_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3107_; 
v___x_3083_ = lean_st_ref_take(v_a_3073_);
v_env_3084_ = lean_ctor_get(v___x_3083_, 0);
v_nextMacroScope_3085_ = lean_ctor_get(v___x_3083_, 1);
v_ngen_3086_ = lean_ctor_get(v___x_3083_, 2);
v_auxDeclNGen_3087_ = lean_ctor_get(v___x_3083_, 3);
v_traceState_3088_ = lean_ctor_get(v___x_3083_, 4);
v_messages_3089_ = lean_ctor_get(v___x_3083_, 6);
v_infoState_3090_ = lean_ctor_get(v___x_3083_, 7);
v_snapshotTasks_3091_ = lean_ctor_get(v___x_3083_, 8);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v___x_3083_, 5);
lean_dec(v_unused_3108_);
v___x_3093_ = v___x_3083_;
v_isShared_3094_ = v_isSharedCheck_3107_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_snapshotTasks_3091_);
lean_inc(v_infoState_3090_);
lean_inc(v_messages_3089_);
lean_inc(v_traceState_3088_);
lean_inc(v_auxDeclNGen_3087_);
lean_inc(v_ngen_3086_);
lean_inc(v_nextMacroScope_3085_);
lean_inc(v_env_3084_);
lean_dec(v___x_3083_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3107_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3100_; 
v___x_3095_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3076_);
v___x_3096_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3096_, 0, v_declName_3076_);
lean_ctor_set(v___x_3096_, 1, v_levelParams_3075_);
lean_ctor_set(v___x_3096_, 2, v_type_3077_);
lean_ctor_set(v___x_3096_, 3, v_value_3078_);
lean_ctor_set(v___x_3096_, 4, v_recArgPos_3070_);
lean_ctor_set(v___x_3096_, 5, v_declNames_3069_);
lean_ctor_set(v___x_3096_, 6, v_fixedParamPerms_3071_);
v___x_3097_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3095_, v_env_3084_, v_declName_3076_, v___x_3096_);
v___x_3098_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 5, v___x_3098_);
lean_ctor_set(v___x_3093_, 0, v___x_3097_);
v___x_3100_ = v___x_3093_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_nextMacroScope_3085_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v_ngen_3086_);
lean_ctor_set(v_reuseFailAlloc_3106_, 3, v_auxDeclNGen_3087_);
lean_ctor_set(v_reuseFailAlloc_3106_, 4, v_traceState_3088_);
lean_ctor_set(v_reuseFailAlloc_3106_, 5, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3106_, 6, v_messages_3089_);
lean_ctor_set(v_reuseFailAlloc_3106_, 7, v_infoState_3090_);
lean_ctor_set(v_reuseFailAlloc_3106_, 8, v_snapshotTasks_3091_);
v___x_3100_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3101_ = lean_st_ref_put(v_a_3073_, v___x_3100_);
v___x_3102_ = lean_box(0);
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 0, v___x_3102_);
v___x_3104_ = v___x_3081_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
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
}
else
{
lean_dec_ref(v_value_3078_);
lean_dec_ref(v_type_3077_);
lean_dec(v_declName_3076_);
lean_dec(v_levelParams_3075_);
lean_dec_ref(v_fixedParamPerms_3071_);
lean_dec(v_recArgPos_3070_);
lean_dec_ref(v_declNames_3069_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3111_, lean_object* v_declNames_3112_, lean_object* v_recArgPos_3113_, lean_object* v_fixedParamPerms_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v_res_3118_; 
v_res_3118_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3111_, v_declNames_3112_, v_recArgPos_3113_, v_fixedParamPerms_3114_, v_a_3115_, v_a_3116_);
lean_dec(v_a_3116_);
lean_dec_ref(v_a_3115_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3119_, lean_object* v_k_3120_, uint8_t v_cleanupAnnotations_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v___f_3127_; uint8_t v___x_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___f_3127_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3127_, 0, v_k_3120_);
v___x_3128_ = 1;
v___x_3129_ = 0;
v___x_3130_ = lean_box(0);
v___x_3131_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3119_, v___x_3128_, v___x_3129_, v___x_3128_, v___x_3129_, v___x_3130_, v___f_3127_, v_cleanupAnnotations_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3131_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3131_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3148_, lean_object* v_k_3149_, lean_object* v_cleanupAnnotations_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3156_; lean_object* v_res_3157_; 
v_cleanupAnnotations_boxed_3156_ = lean_unbox(v_cleanupAnnotations_3150_);
v_res_3157_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3148_, v_k_3149_, v_cleanupAnnotations_boxed_3156_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3158_, lean_object* v_e_3159_, lean_object* v_k_3160_, uint8_t v_cleanupAnnotations_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3159_, v_k_3160_, v_cleanupAnnotations_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3168_, lean_object* v_e_3169_, lean_object* v_k_3170_, lean_object* v_cleanupAnnotations_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3177_; lean_object* v_res_3178_; 
v_cleanupAnnotations_boxed_3177_ = lean_unbox(v_cleanupAnnotations_3171_);
v_res_3178_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3168_, v_e_3169_, v_k_3170_, v_cleanupAnnotations_boxed_3177_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3179_, uint8_t v_isExporting_3180_, lean_object* v___x_3181_, lean_object* v___y_3182_, lean_object* v___x_3183_, lean_object* v_a_x3f_3184_){
_start:
{
lean_object* v___x_3186_; lean_object* v_env_3187_; lean_object* v_nextMacroScope_3188_; lean_object* v_ngen_3189_; lean_object* v_auxDeclNGen_3190_; lean_object* v_traceState_3191_; lean_object* v_messages_3192_; lean_object* v_infoState_3193_; lean_object* v_snapshotTasks_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3219_; 
v___x_3186_ = lean_st_ref_take(v___y_3179_);
v_env_3187_ = lean_ctor_get(v___x_3186_, 0);
v_nextMacroScope_3188_ = lean_ctor_get(v___x_3186_, 1);
v_ngen_3189_ = lean_ctor_get(v___x_3186_, 2);
v_auxDeclNGen_3190_ = lean_ctor_get(v___x_3186_, 3);
v_traceState_3191_ = lean_ctor_get(v___x_3186_, 4);
v_messages_3192_ = lean_ctor_get(v___x_3186_, 6);
v_infoState_3193_ = lean_ctor_get(v___x_3186_, 7);
v_snapshotTasks_3194_ = lean_ctor_get(v___x_3186_, 8);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v___x_3186_, 5);
lean_dec(v_unused_3220_);
v___x_3196_ = v___x_3186_;
v_isShared_3197_ = v_isSharedCheck_3219_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_snapshotTasks_3194_);
lean_inc(v_infoState_3193_);
lean_inc(v_messages_3192_);
lean_inc(v_traceState_3191_);
lean_inc(v_auxDeclNGen_3190_);
lean_inc(v_ngen_3189_);
lean_inc(v_nextMacroScope_3188_);
lean_inc(v_env_3187_);
lean_dec(v___x_3186_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3219_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = l_Lean_Environment_setExporting(v_env_3187_, v_isExporting_3180_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 5, v___x_3181_);
lean_ctor_set(v___x_3196_, 0, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_nextMacroScope_3188_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_ngen_3189_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_auxDeclNGen_3190_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_traceState_3191_);
lean_ctor_set(v_reuseFailAlloc_3218_, 5, v___x_3181_);
lean_ctor_set(v_reuseFailAlloc_3218_, 6, v_messages_3192_);
lean_ctor_set(v_reuseFailAlloc_3218_, 7, v_infoState_3193_);
lean_ctor_set(v_reuseFailAlloc_3218_, 8, v_snapshotTasks_3194_);
v___x_3200_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v_mctx_3203_; lean_object* v_zetaDeltaFVarIds_3204_; lean_object* v_postponed_3205_; lean_object* v_diag_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3216_; 
v___x_3201_ = lean_st_ref_put(v___y_3179_, v___x_3200_);
v___x_3202_ = lean_st_ref_take(v___y_3182_);
v_mctx_3203_ = lean_ctor_get(v___x_3202_, 0);
v_zetaDeltaFVarIds_3204_ = lean_ctor_get(v___x_3202_, 2);
v_postponed_3205_ = lean_ctor_get(v___x_3202_, 3);
v_diag_3206_ = lean_ctor_get(v___x_3202_, 4);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3216_ == 0)
{
lean_object* v_unused_3217_; 
v_unused_3217_ = lean_ctor_get(v___x_3202_, 1);
lean_dec(v_unused_3217_);
v___x_3208_ = v___x_3202_;
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_diag_3206_);
lean_inc(v_postponed_3205_);
lean_inc(v_zetaDeltaFVarIds_3204_);
lean_inc(v_mctx_3203_);
lean_dec(v___x_3202_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3216_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 1, v___x_3183_);
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_mctx_3203_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3215_, 2, v_zetaDeltaFVarIds_3204_);
lean_ctor_set(v_reuseFailAlloc_3215_, 3, v_postponed_3205_);
lean_ctor_set(v_reuseFailAlloc_3215_, 4, v_diag_3206_);
v___x_3211_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_st_ref_put(v___y_3182_, v___x_3211_);
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3221_, lean_object* v_isExporting_3222_, lean_object* v___x_3223_, lean_object* v___y_3224_, lean_object* v___x_3225_, lean_object* v_a_x3f_3226_, lean_object* v___y_3227_){
_start:
{
uint8_t v_isExporting_boxed_3228_; lean_object* v_res_3229_; 
v_isExporting_boxed_3228_ = lean_unbox(v_isExporting_3222_);
v_res_3229_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3221_, v_isExporting_boxed_3228_, v___x_3223_, v___y_3224_, v___x_3225_, v_a_x3f_3226_);
lean_dec(v_a_x3f_3226_);
lean_dec(v___y_3224_);
lean_dec(v___y_3221_);
return v_res_3229_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3231_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
lean_ctor_set(v___x_3231_, 2, v___x_3230_);
lean_ctor_set(v___x_3231_, 3, v___x_3230_);
lean_ctor_set(v___x_3231_, 4, v___x_3230_);
lean_ctor_set(v___x_3231_, 5, v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3232_, uint8_t v_isExporting_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; lean_object* v_env_3240_; lean_object* v___x_3241_; uint8_t v_isModule_3242_; 
v___x_3239_ = lean_st_ref_get(v___y_3237_);
v_env_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc_ref(v_env_3240_);
lean_dec(v___x_3239_);
v___x_3241_ = l_Lean_Environment_header(v_env_3240_);
v_isModule_3242_ = lean_ctor_get_uint8(v___x_3241_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3241_);
if (v_isModule_3242_ == 0)
{
lean_object* v___x_3243_; 
lean_dec_ref(v_env_3240_);
lean_inc(v___y_3237_);
lean_inc_ref(v___y_3236_);
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3234_);
v___x_3243_ = lean_apply_5(v_x_3232_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, lean_box(0));
return v___x_3243_;
}
else
{
uint8_t v_isExporting_3244_; 
v_isExporting_3244_ = lean_ctor_get_uint8(v_env_3240_, sizeof(void*)*8);
lean_dec_ref(v_env_3240_);
if (v_isExporting_3233_ == 0)
{
if (v_isExporting_3244_ == 0)
{
lean_object* v___x_3310_; 
lean_inc(v___y_3237_);
lean_inc_ref(v___y_3236_);
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3234_);
v___x_3310_ = lean_apply_5(v_x_3232_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, lean_box(0));
return v___x_3310_;
}
else
{
goto v___jp_3245_;
}
}
else
{
if (v_isExporting_3244_ == 0)
{
goto v___jp_3245_;
}
else
{
lean_object* v___x_3311_; 
lean_inc(v___y_3237_);
lean_inc_ref(v___y_3236_);
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3234_);
v___x_3311_ = lean_apply_5(v_x_3232_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, lean_box(0));
return v___x_3311_;
}
}
v___jp_3245_:
{
lean_object* v___x_3246_; lean_object* v_env_3247_; lean_object* v_nextMacroScope_3248_; lean_object* v_ngen_3249_; lean_object* v_auxDeclNGen_3250_; lean_object* v_traceState_3251_; lean_object* v_messages_3252_; lean_object* v_infoState_3253_; lean_object* v_snapshotTasks_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3308_; 
v___x_3246_ = lean_st_ref_take(v___y_3237_);
v_env_3247_ = lean_ctor_get(v___x_3246_, 0);
v_nextMacroScope_3248_ = lean_ctor_get(v___x_3246_, 1);
v_ngen_3249_ = lean_ctor_get(v___x_3246_, 2);
v_auxDeclNGen_3250_ = lean_ctor_get(v___x_3246_, 3);
v_traceState_3251_ = lean_ctor_get(v___x_3246_, 4);
v_messages_3252_ = lean_ctor_get(v___x_3246_, 6);
v_infoState_3253_ = lean_ctor_get(v___x_3246_, 7);
v_snapshotTasks_3254_ = lean_ctor_get(v___x_3246_, 8);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3308_ == 0)
{
lean_object* v_unused_3309_; 
v_unused_3309_ = lean_ctor_get(v___x_3246_, 5);
lean_dec(v_unused_3309_);
v___x_3256_ = v___x_3246_;
v_isShared_3257_ = v_isSharedCheck_3308_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_snapshotTasks_3254_);
lean_inc(v_infoState_3253_);
lean_inc(v_messages_3252_);
lean_inc(v_traceState_3251_);
lean_inc(v_auxDeclNGen_3250_);
lean_inc(v_ngen_3249_);
lean_inc(v_nextMacroScope_3248_);
lean_inc(v_env_3247_);
lean_dec(v___x_3246_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3308_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3258_ = l_Lean_Environment_setExporting(v_env_3247_, v_isExporting_3233_);
v___x_3259_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 5, v___x_3259_);
lean_ctor_set(v___x_3256_, 0, v___x_3258_);
v___x_3261_ = v___x_3256_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3307_, 1, v_nextMacroScope_3248_);
lean_ctor_set(v_reuseFailAlloc_3307_, 2, v_ngen_3249_);
lean_ctor_set(v_reuseFailAlloc_3307_, 3, v_auxDeclNGen_3250_);
lean_ctor_set(v_reuseFailAlloc_3307_, 4, v_traceState_3251_);
lean_ctor_set(v_reuseFailAlloc_3307_, 5, v___x_3259_);
lean_ctor_set(v_reuseFailAlloc_3307_, 6, v_messages_3252_);
lean_ctor_set(v_reuseFailAlloc_3307_, 7, v_infoState_3253_);
lean_ctor_set(v_reuseFailAlloc_3307_, 8, v_snapshotTasks_3254_);
v___x_3261_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v_mctx_3264_; lean_object* v_zetaDeltaFVarIds_3265_; lean_object* v_postponed_3266_; lean_object* v_diag_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3305_; 
v___x_3262_ = lean_st_ref_put(v___y_3237_, v___x_3261_);
v___x_3263_ = lean_st_ref_take(v___y_3235_);
v_mctx_3264_ = lean_ctor_get(v___x_3263_, 0);
v_zetaDeltaFVarIds_3265_ = lean_ctor_get(v___x_3263_, 2);
v_postponed_3266_ = lean_ctor_get(v___x_3263_, 3);
v_diag_3267_ = lean_ctor_get(v___x_3263_, 4);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; 
v_unused_3306_ = lean_ctor_get(v___x_3263_, 1);
lean_dec(v_unused_3306_);
v___x_3269_ = v___x_3263_;
v_isShared_3270_ = v_isSharedCheck_3305_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_diag_3267_);
lean_inc(v_postponed_3266_);
lean_inc(v_zetaDeltaFVarIds_3265_);
lean_inc(v_mctx_3264_);
lean_dec(v___x_3263_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3305_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 1, v___x_3271_);
v___x_3273_ = v___x_3269_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_mctx_3264_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v___x_3271_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_zetaDeltaFVarIds_3265_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_postponed_3266_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_diag_3267_);
v___x_3273_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; lean_object* v_r_3275_; 
v___x_3274_ = lean_st_ref_put(v___y_3235_, v___x_3273_);
lean_inc(v___y_3237_);
lean_inc_ref(v___y_3236_);
lean_inc(v___y_3235_);
lean_inc_ref(v___y_3234_);
v_r_3275_ = lean_apply_5(v_x_3232_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, lean_box(0));
if (lean_obj_tag(v_r_3275_) == 0)
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3292_; 
v_a_3276_ = lean_ctor_get(v_r_3275_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_r_3275_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3278_ = v_r_3275_;
v_isShared_3279_ = v_isSharedCheck_3292_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v_r_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3292_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
lean_inc(v_a_3276_);
if (v_isShared_3279_ == 0)
{
lean_ctor_set_tag(v___x_3278_, 1);
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
v___x_3282_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3237_, v_isExporting_3244_, v___x_3259_, v___y_3235_, v___x_3271_, v___x_3281_);
lean_dec_ref(v___x_3281_);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; 
v_unused_3290_ = lean_ctor_get(v___x_3282_, 0);
lean_dec(v_unused_3290_);
v___x_3284_ = v___x_3282_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_dec(v___x_3282_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v_a_3276_);
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3276_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
v_a_3293_ = lean_ctor_get(v_r_3275_, 0);
lean_inc(v_a_3293_);
lean_dec_ref_known(v_r_3275_, 1);
v___x_3294_ = lean_box(0);
v___x_3295_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3237_, v_isExporting_3244_, v___x_3259_, v___y_3235_, v___x_3271_, v___x_3294_);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3302_ == 0)
{
lean_object* v_unused_3303_; 
v_unused_3303_ = lean_ctor_get(v___x_3295_, 0);
lean_dec(v_unused_3303_);
v___x_3297_ = v___x_3295_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_dec(v___x_3295_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 1);
lean_ctor_set(v___x_3297_, 0, v_a_3293_);
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3293_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3312_, lean_object* v_isExporting_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
uint8_t v_isExporting_boxed_3319_; lean_object* v_res_3320_; 
v_isExporting_boxed_3319_ = lean_unbox(v_isExporting_3313_);
v_res_3320_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3312_, v_isExporting_boxed_3319_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3321_, uint8_t v_when_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
if (v_when_3322_ == 0)
{
lean_object* v___x_3328_; 
lean_inc(v___y_3326_);
lean_inc_ref(v___y_3325_);
lean_inc(v___y_3324_);
lean_inc_ref(v___y_3323_);
v___x_3328_ = lean_apply_5(v_x_3321_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, lean_box(0));
return v___x_3328_;
}
else
{
uint8_t v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = 0;
v___x_3330_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3321_, v___x_3329_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
return v___x_3330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3331_, lean_object* v_when_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
uint8_t v_when_boxed_3338_; lean_object* v_res_3339_; 
v_when_boxed_3338_ = lean_unbox(v_when_3332_);
v_res_3339_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3331_, v_when_boxed_3338_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
if (lean_obj_tag(v_a_3340_) == 0)
{
lean_object* v___x_3342_; 
v___x_3342_ = l_List_reverse___redArg(v_a_3341_);
return v___x_3342_;
}
else
{
lean_object* v_head_3343_; lean_object* v_tail_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3353_; 
v_head_3343_ = lean_ctor_get(v_a_3340_, 0);
v_tail_3344_ = lean_ctor_get(v_a_3340_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_a_3340_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3346_ = v_a_3340_;
v_isShared_3347_ = v_isSharedCheck_3353_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_tail_3344_);
lean_inc(v_head_3343_);
lean_dec(v_a_3340_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3353_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3350_; 
v___x_3348_ = l_Lean_mkLevelParam(v_head_3343_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 1, v_a_3341_);
lean_ctor_set(v___x_3346_, 0, v___x_3348_);
v___x_3350_ = v___x_3346_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3352_, 1, v_a_3341_);
v___x_3350_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
v_a_3340_ = v_tail_3344_;
v_a_3341_ = v___x_3350_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3354_, lean_object* v_declName_3355_, lean_object* v_name_3356_, lean_object* v_xs_3357_, lean_object* v_body_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_){
_start:
{
lean_object* v___x_3364_; lean_object* v_us_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3364_ = lean_box(0);
lean_inc(v_levelParams_3354_);
v_us_3365_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3354_, v___x_3364_);
lean_inc(v_declName_3355_);
v___x_3366_ = l_Lean_mkConst(v_declName_3355_, v_us_3365_);
v___x_3367_ = l_Lean_mkAppN(v___x_3366_, v_xs_3357_);
v___x_3368_ = l_Lean_Meta_mkEq(v___x_3367_, v_body_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; lean_object* v___x_3372_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc_n(v_a_3369_, 2);
lean_dec_ref_known(v___x_3368_, 1);
v___x_3370_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3370_, 0, v_declName_3355_);
lean_closure_set(v___x_3370_, 1, v_a_3369_);
v___x_3371_ = 1;
v___x_3372_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3370_, v___x_3371_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; uint8_t v___x_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v___x_3374_ = 0;
v___x_3375_ = 1;
v___x_3376_ = l_Lean_Meta_mkForallFVars(v_xs_3357_, v_a_3369_, v___x_3374_, v___x_3371_, v___x_3371_, v___x_3375_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = l_Lean_Meta_letToHave(v_a_3377_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v___x_3380_ = l_Lean_Meta_mkLambdaFVars(v_xs_3357_, v_a_3373_, v___x_3374_, v___x_3371_, v___x_3374_, v___x_3371_, v___x_3375_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
lean_inc_n(v_name_3356_, 2);
v___x_3382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3382_, 0, v_name_3356_);
lean_ctor_set(v___x_3382_, 1, v_levelParams_3354_);
lean_ctor_set(v___x_3382_, 2, v_a_3379_);
v___x_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3383_, 0, v_name_3356_);
lean_ctor_set(v___x_3383_, 1, v___x_3364_);
v___x_3384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3382_);
lean_ctor_set(v___x_3384_, 1, v_a_3381_);
lean_ctor_set(v___x_3384_, 2, v___x_3383_);
v___x_3385_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
v___x_3386_ = l_Lean_addDecl(v___x_3385_, v___x_3374_, v___y_3361_, v___y_3362_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v___x_3387_; 
lean_dec_ref_known(v___x_3386_, 1);
v___x_3387_ = l_Lean_inferDefEqAttr(v_name_3356_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_);
return v___x_3387_;
}
else
{
lean_dec(v_name_3356_);
return v___x_3386_;
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v_a_3379_);
lean_dec(v_name_3356_);
lean_dec(v_levelParams_3354_);
v_a_3388_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3380_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3380_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec(v_a_3373_);
lean_dec(v_name_3356_);
lean_dec(v_levelParams_3354_);
v_a_3396_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3378_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3378_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec(v_a_3373_);
lean_dec(v_name_3356_);
lean_dec(v_levelParams_3354_);
v_a_3404_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3376_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3376_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec(v_a_3369_);
lean_dec(v_name_3356_);
lean_dec(v_levelParams_3354_);
v_a_3412_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3372_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3372_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec(v_name_3356_);
lean_dec(v_declName_3355_);
lean_dec(v_levelParams_3354_);
v_a_3420_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3368_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3368_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3428_, lean_object* v_declName_3429_, lean_object* v_name_3430_, lean_object* v_xs_3431_, lean_object* v_body_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3428_, v_declName_3429_, v_name_3430_, v_xs_3431_, v_body_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec_ref(v_xs_3431_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3439_, lean_object* v_k_3440_, uint8_t v_v_3441_){
_start:
{
lean_object* v_map_3442_; uint8_t v_hasTrace_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3457_; 
v_map_3442_ = lean_ctor_get(v_o_3439_, 0);
v_hasTrace_3443_ = lean_ctor_get_uint8(v_o_3439_, sizeof(void*)*1);
v_isSharedCheck_3457_ = !lean_is_exclusive(v_o_3439_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3445_ = v_o_3439_;
v_isShared_3446_ = v_isSharedCheck_3457_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_map_3442_);
lean_dec(v_o_3439_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3457_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3447_, 0, v_v_3441_);
lean_inc(v_k_3440_);
v___x_3448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3440_, v___x_3447_, v_map_3442_);
if (v_hasTrace_3443_ == 0)
{
lean_object* v___x_3449_; uint8_t v___x_3450_; lean_object* v___x_3452_; 
v___x_3449_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3450_ = l_Lean_Name_isPrefixOf(v___x_3449_, v_k_3440_);
lean_dec(v_k_3440_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3448_);
v___x_3452_ = v___x_3445_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3448_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_ctor_set_uint8(v___x_3452_, sizeof(void*)*1, v___x_3450_);
return v___x_3452_;
}
}
else
{
lean_object* v___x_3455_; 
lean_dec(v_k_3440_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3448_);
v___x_3455_ = v___x_3445_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3448_);
lean_ctor_set_uint8(v_reuseFailAlloc_3456_, sizeof(void*)*1, v_hasTrace_3443_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3458_, lean_object* v_k_3459_, lean_object* v_v_3460_){
_start:
{
uint8_t v_v_boxed_3461_; lean_object* v_res_3462_; 
v_v_boxed_3461_ = lean_unbox(v_v_3460_);
v_res_3462_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3458_, v_k_3459_, v_v_boxed_3461_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3463_, lean_object* v_opt_3464_, uint8_t v_val_3465_){
_start:
{
lean_object* v_name_3466_; lean_object* v___x_3467_; 
v_name_3466_ = lean_ctor_get(v_opt_3464_, 0);
lean_inc(v_name_3466_);
lean_dec_ref(v_opt_3464_);
v___x_3467_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3463_, v_name_3466_, v_val_3465_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3468_, lean_object* v_opt_3469_, lean_object* v_val_3470_){
_start:
{
uint8_t v_val_boxed_3471_; lean_object* v_res_3472_; 
v_val_boxed_3471_ = lean_unbox(v_val_3470_);
v_res_3472_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3468_, v_opt_3469_, v_val_boxed_3471_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3473_, lean_object* v_info_3474_, lean_object* v_name_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v___x_3481_; lean_object* v_toCold_3482_; lean_object* v_levelParams_3483_; lean_object* v_value_3484_; lean_object* v_currRecDepth_3485_; lean_object* v_ref_3486_; uint8_t v_suppressElabErrors_3487_; lean_object* v_fileName_3488_; lean_object* v_fileMap_3489_; lean_object* v_options_3490_; lean_object* v_currNamespace_3491_; lean_object* v_openDecls_3492_; lean_object* v_initHeartbeats_3493_; lean_object* v_maxHeartbeats_3494_; lean_object* v_quotContext_3495_; lean_object* v_currMacroScope_3496_; lean_object* v_cancelTk_x3f_3497_; lean_object* v_inheritedTraceOptions_3498_; lean_object* v_env_3499_; lean_object* v___f_3500_; uint8_t v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; lean_object* v_fileName_3507_; lean_object* v_fileMap_3508_; lean_object* v_currNamespace_3509_; lean_object* v_openDecls_3510_; lean_object* v_initHeartbeats_3511_; lean_object* v_maxHeartbeats_3512_; lean_object* v_quotContext_3513_; lean_object* v_currMacroScope_3514_; lean_object* v_cancelTk_x3f_3515_; lean_object* v_inheritedTraceOptions_3516_; lean_object* v_currRecDepth_3517_; lean_object* v_ref_3518_; uint8_t v_suppressElabErrors_3519_; lean_object* v___y_3520_; uint8_t v___y_3527_; uint8_t v___x_3548_; 
v___x_3481_ = lean_st_ref_get(v_a_3479_);
v_toCold_3482_ = lean_ctor_get(v_a_3478_, 0);
v_levelParams_3483_ = lean_ctor_get(v_info_3474_, 1);
lean_inc(v_levelParams_3483_);
v_value_3484_ = lean_ctor_get(v_info_3474_, 3);
lean_inc_ref(v_value_3484_);
lean_dec_ref(v_info_3474_);
v_currRecDepth_3485_ = lean_ctor_get(v_a_3478_, 1);
v_ref_3486_ = lean_ctor_get(v_a_3478_, 2);
v_suppressElabErrors_3487_ = lean_ctor_get_uint8(v_a_3478_, sizeof(void*)*3 + 1);
v_fileName_3488_ = lean_ctor_get(v_toCold_3482_, 0);
v_fileMap_3489_ = lean_ctor_get(v_toCold_3482_, 1);
v_options_3490_ = lean_ctor_get(v_toCold_3482_, 2);
v_currNamespace_3491_ = lean_ctor_get(v_toCold_3482_, 4);
v_openDecls_3492_ = lean_ctor_get(v_toCold_3482_, 5);
v_initHeartbeats_3493_ = lean_ctor_get(v_toCold_3482_, 6);
v_maxHeartbeats_3494_ = lean_ctor_get(v_toCold_3482_, 7);
v_quotContext_3495_ = lean_ctor_get(v_toCold_3482_, 8);
v_currMacroScope_3496_ = lean_ctor_get(v_toCold_3482_, 9);
v_cancelTk_x3f_3497_ = lean_ctor_get(v_toCold_3482_, 10);
v_inheritedTraceOptions_3498_ = lean_ctor_get(v_toCold_3482_, 11);
v_env_3499_ = lean_ctor_get(v___x_3481_, 0);
lean_inc_ref(v_env_3499_);
lean_dec(v___x_3481_);
v___f_3500_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3500_, 0, v_levelParams_3483_);
lean_closure_set(v___f_3500_, 1, v_declName_3473_);
lean_closure_set(v___f_3500_, 2, v_name_3475_);
v___x_3501_ = 0;
v___x_3502_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3490_);
v___x_3503_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3490_, v___x_3502_, v___x_3501_);
v___x_3504_ = l_Lean_diagnostics;
v___x_3505_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v___x_3503_, v___x_3504_);
v___x_3548_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3499_);
lean_dec_ref(v_env_3499_);
if (v___x_3505_ == 0)
{
if (v___x_3548_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_3498_);
lean_inc(v_cancelTk_x3f_3497_);
lean_inc(v_currMacroScope_3496_);
lean_inc(v_quotContext_3495_);
lean_inc(v_maxHeartbeats_3494_);
lean_inc(v_initHeartbeats_3493_);
lean_inc(v_openDecls_3492_);
lean_inc(v_currNamespace_3491_);
lean_inc_ref(v_fileMap_3489_);
lean_inc_ref(v_fileName_3488_);
v_fileName_3507_ = v_fileName_3488_;
v_fileMap_3508_ = v_fileMap_3489_;
v_currNamespace_3509_ = v_currNamespace_3491_;
v_openDecls_3510_ = v_openDecls_3492_;
v_initHeartbeats_3511_ = v_initHeartbeats_3493_;
v_maxHeartbeats_3512_ = v_maxHeartbeats_3494_;
v_quotContext_3513_ = v_quotContext_3495_;
v_currMacroScope_3514_ = v_currMacroScope_3496_;
v_cancelTk_x3f_3515_ = v_cancelTk_x3f_3497_;
v_inheritedTraceOptions_3516_ = v_inheritedTraceOptions_3498_;
v_currRecDepth_3517_ = v_currRecDepth_3485_;
v_ref_3518_ = v_ref_3486_;
v_suppressElabErrors_3519_ = v_suppressElabErrors_3487_;
v___y_3520_ = v_a_3479_;
goto v___jp_3506_;
}
else
{
v___y_3527_ = v___x_3505_;
goto v___jp_3526_;
}
}
else
{
v___y_3527_ = v___x_3548_;
goto v___jp_3526_;
}
v___jp_3506_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3521_ = l_Lean_maxRecDepth;
v___x_3522_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___x_3503_, v___x_3521_);
v___x_3523_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3523_, 0, v_fileName_3507_);
lean_ctor_set(v___x_3523_, 1, v_fileMap_3508_);
lean_ctor_set(v___x_3523_, 2, v___x_3503_);
lean_ctor_set(v___x_3523_, 3, v___x_3522_);
lean_ctor_set(v___x_3523_, 4, v_currNamespace_3509_);
lean_ctor_set(v___x_3523_, 5, v_openDecls_3510_);
lean_ctor_set(v___x_3523_, 6, v_initHeartbeats_3511_);
lean_ctor_set(v___x_3523_, 7, v_maxHeartbeats_3512_);
lean_ctor_set(v___x_3523_, 8, v_quotContext_3513_);
lean_ctor_set(v___x_3523_, 9, v_currMacroScope_3514_);
lean_ctor_set(v___x_3523_, 10, v_cancelTk_x3f_3515_);
lean_ctor_set(v___x_3523_, 11, v_inheritedTraceOptions_3516_);
lean_inc(v_ref_3518_);
lean_inc(v_currRecDepth_3517_);
v___x_3524_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v_currRecDepth_3517_);
lean_ctor_set(v___x_3524_, 2, v_ref_3518_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*3, v___x_3505_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*3 + 1, v_suppressElabErrors_3519_);
v___x_3525_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3484_, v___f_3500_, v___x_3501_, v_a_3476_, v_a_3477_, v___x_3524_, v___y_3520_);
lean_dec_ref_known(v___x_3524_, 3);
return v___x_3525_;
}
v___jp_3526_:
{
if (v___y_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v_env_3529_; lean_object* v_nextMacroScope_3530_; lean_object* v_ngen_3531_; lean_object* v_auxDeclNGen_3532_; lean_object* v_traceState_3533_; lean_object* v_messages_3534_; lean_object* v_infoState_3535_; lean_object* v_snapshotTasks_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3546_; 
v___x_3528_ = lean_st_ref_take(v_a_3479_);
v_env_3529_ = lean_ctor_get(v___x_3528_, 0);
v_nextMacroScope_3530_ = lean_ctor_get(v___x_3528_, 1);
v_ngen_3531_ = lean_ctor_get(v___x_3528_, 2);
v_auxDeclNGen_3532_ = lean_ctor_get(v___x_3528_, 3);
v_traceState_3533_ = lean_ctor_get(v___x_3528_, 4);
v_messages_3534_ = lean_ctor_get(v___x_3528_, 6);
v_infoState_3535_ = lean_ctor_get(v___x_3528_, 7);
v_snapshotTasks_3536_ = lean_ctor_get(v___x_3528_, 8);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3546_ == 0)
{
lean_object* v_unused_3547_; 
v_unused_3547_ = lean_ctor_get(v___x_3528_, 5);
lean_dec(v_unused_3547_);
v___x_3538_ = v___x_3528_;
v_isShared_3539_ = v_isSharedCheck_3546_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_snapshotTasks_3536_);
lean_inc(v_infoState_3535_);
lean_inc(v_messages_3534_);
lean_inc(v_traceState_3533_);
lean_inc(v_auxDeclNGen_3532_);
lean_inc(v_ngen_3531_);
lean_inc(v_nextMacroScope_3530_);
lean_inc(v_env_3529_);
lean_dec(v___x_3528_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3546_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3540_ = l_Lean_Kernel_enableDiag(v_env_3529_, v___x_3505_);
v___x_3541_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3539_ == 0)
{
lean_ctor_set(v___x_3538_, 5, v___x_3541_);
lean_ctor_set(v___x_3538_, 0, v___x_3540_);
v___x_3543_ = v___x_3538_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3540_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_nextMacroScope_3530_);
lean_ctor_set(v_reuseFailAlloc_3545_, 2, v_ngen_3531_);
lean_ctor_set(v_reuseFailAlloc_3545_, 3, v_auxDeclNGen_3532_);
lean_ctor_set(v_reuseFailAlloc_3545_, 4, v_traceState_3533_);
lean_ctor_set(v_reuseFailAlloc_3545_, 5, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3545_, 6, v_messages_3534_);
lean_ctor_set(v_reuseFailAlloc_3545_, 7, v_infoState_3535_);
lean_ctor_set(v_reuseFailAlloc_3545_, 8, v_snapshotTasks_3536_);
v___x_3543_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; 
v___x_3544_ = lean_st_ref_put(v_a_3479_, v___x_3543_);
lean_inc_ref(v_inheritedTraceOptions_3498_);
lean_inc(v_cancelTk_x3f_3497_);
lean_inc(v_currMacroScope_3496_);
lean_inc(v_quotContext_3495_);
lean_inc(v_maxHeartbeats_3494_);
lean_inc(v_initHeartbeats_3493_);
lean_inc(v_openDecls_3492_);
lean_inc(v_currNamespace_3491_);
lean_inc_ref(v_fileMap_3489_);
lean_inc_ref(v_fileName_3488_);
v_fileName_3507_ = v_fileName_3488_;
v_fileMap_3508_ = v_fileMap_3489_;
v_currNamespace_3509_ = v_currNamespace_3491_;
v_openDecls_3510_ = v_openDecls_3492_;
v_initHeartbeats_3511_ = v_initHeartbeats_3493_;
v_maxHeartbeats_3512_ = v_maxHeartbeats_3494_;
v_quotContext_3513_ = v_quotContext_3495_;
v_currMacroScope_3514_ = v_currMacroScope_3496_;
v_cancelTk_x3f_3515_ = v_cancelTk_x3f_3497_;
v_inheritedTraceOptions_3516_ = v_inheritedTraceOptions_3498_;
v_currRecDepth_3517_ = v_currRecDepth_3485_;
v_ref_3518_ = v_ref_3486_;
v_suppressElabErrors_3519_ = v_suppressElabErrors_3487_;
v___y_3520_ = v_a_3479_;
goto v___jp_3506_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_3498_);
lean_inc(v_cancelTk_x3f_3497_);
lean_inc(v_currMacroScope_3496_);
lean_inc(v_quotContext_3495_);
lean_inc(v_maxHeartbeats_3494_);
lean_inc(v_initHeartbeats_3493_);
lean_inc(v_openDecls_3492_);
lean_inc(v_currNamespace_3491_);
lean_inc_ref(v_fileMap_3489_);
lean_inc_ref(v_fileName_3488_);
v_fileName_3507_ = v_fileName_3488_;
v_fileMap_3508_ = v_fileMap_3489_;
v_currNamespace_3509_ = v_currNamespace_3491_;
v_openDecls_3510_ = v_openDecls_3492_;
v_initHeartbeats_3511_ = v_initHeartbeats_3493_;
v_maxHeartbeats_3512_ = v_maxHeartbeats_3494_;
v_quotContext_3513_ = v_quotContext_3495_;
v_currMacroScope_3514_ = v_currMacroScope_3496_;
v_cancelTk_x3f_3515_ = v_cancelTk_x3f_3497_;
v_inheritedTraceOptions_3516_ = v_inheritedTraceOptions_3498_;
v_currRecDepth_3517_ = v_currRecDepth_3485_;
v_ref_3518_ = v_ref_3486_;
v_suppressElabErrors_3519_ = v_suppressElabErrors_3487_;
v___y_3520_ = v_a_3479_;
goto v___jp_3506_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3549_, lean_object* v_info_3550_, lean_object* v_name_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3549_, v_info_3550_, v_name_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_);
lean_dec(v_a_3555_);
lean_dec_ref(v_a_3554_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3558_, lean_object* v_x_3559_, uint8_t v_isExporting_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3559_, v_isExporting_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3567_, lean_object* v_x_3568_, lean_object* v_isExporting_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
uint8_t v_isExporting_boxed_3575_; lean_object* v_res_3576_; 
v_isExporting_boxed_3575_ = lean_unbox(v_isExporting_3569_);
v_res_3576_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3567_, v_x_3568_, v_isExporting_boxed_3575_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3577_, lean_object* v_x_3578_, uint8_t v_when_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3578_, v_when_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3586_, lean_object* v_x_3587_, lean_object* v_when_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
uint8_t v_when_boxed_3594_; lean_object* v_res_3595_; 
v_when_boxed_3594_ = lean_unbox(v_when_3588_);
v_res_3595_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3586_, v_x_3587_, v_when_boxed_3594_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3596_, lean_object* v_info_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v___x_3603_; lean_object* v_env_3604_; lean_object* v_declName_3605_; lean_object* v_declNames_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3603_ = lean_st_ref_get(v_a_3601_);
v_env_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc_ref(v_env_3604_);
lean_dec(v___x_3603_);
v_declName_3605_ = lean_ctor_get(v_info_3597_, 0);
v_declNames_3606_ = lean_ctor_get(v_info_3597_, 5);
v___x_3607_ = lean_box(0);
v___x_3608_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3605_);
v___x_3609_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3604_, v_declName_3605_, v___x_3608_);
v___x_3610_ = lean_unsigned_to_nat(0u);
v___x_3611_ = lean_array_get(v___x_3607_, v_declNames_3606_, v___x_3610_);
lean_inc_n(v___x_3609_, 2);
lean_inc(v_declName_3596_);
v___x_3612_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3612_, 0, v_declName_3596_);
lean_closure_set(v___x_3612_, 1, v_info_3597_);
lean_closure_set(v___x_3612_, 2, v___x_3609_);
v___x_3613_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3613_, 0, lean_box(0));
lean_closure_set(v___x_3613_, 1, v_declName_3596_);
lean_closure_set(v___x_3613_, 2, v___x_3612_);
v___x_3614_ = l_Lean_Meta_realizeConst(v___x_3611_, v___x_3609_, v___x_3613_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v___x_3614_, 0);
lean_dec(v_unused_3622_);
v___x_3616_ = v___x_3614_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_dec(v___x_3614_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3609_);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3609_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v___x_3609_);
v_a_3623_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3614_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3614_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3631_, lean_object* v_info_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3631_, v_info_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v_env_3646_; lean_object* v___x_3647_; lean_object* v_toEnvExtension_3648_; lean_object* v_asyncMode_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; lean_object* v___x_3652_; 
v___x_3645_ = lean_st_ref_get(v_a_3643_);
v_env_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc_ref(v_env_3646_);
lean_dec(v___x_3645_);
v___x_3647_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3648_ = lean_ctor_get(v___x_3647_, 0);
v_asyncMode_3649_ = lean_ctor_get(v_toEnvExtension_3648_, 2);
v___x_3650_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3651_ = 0;
lean_inc(v_declName_3639_);
v___x_3652_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3650_, v___x_3647_, v_env_3646_, v_declName_3639_, v_asyncMode_3649_, v___x_3651_);
if (lean_obj_tag(v___x_3652_) == 1)
{
lean_object* v_val_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3677_; 
v_val_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3677_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_val_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3677_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; 
v___x_3657_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3639_, v_val_3653_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3668_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3668_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3668_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v_a_3658_);
v___x_3663_ = v___x_3655_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3665_; 
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3663_);
v___x_3665_ = v___x_3660_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_del_object(v___x_3655_);
v_a_3669_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3657_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3657_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_dec(v___x_3652_);
lean_dec(v_declName_3639_);
v___x_3678_ = lean_box(0);
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_){
_start:
{
lean_object* v_res_3686_; 
v_res_3686_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v___x_3690_; lean_object* v_env_3691_; lean_object* v___x_3692_; lean_object* v_toEnvExtension_3693_; lean_object* v_asyncMode_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; lean_object* v___x_3697_; 
v___x_3690_ = lean_st_ref_get(v_a_3688_);
v_env_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc_ref(v_env_3691_);
lean_dec(v___x_3690_);
v___x_3692_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3693_ = lean_ctor_get(v___x_3692_, 0);
v_asyncMode_3694_ = lean_ctor_get(v_toEnvExtension_3693_, 2);
v___x_3695_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3696_ = 0;
v___x_3697_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3695_, v___x_3692_, v_env_3691_, v_declName_3687_, v_asyncMode_3694_, v___x_3696_);
if (lean_obj_tag(v___x_3697_) == 1)
{
lean_object* v_val_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3707_; 
v_val_3698_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3700_ = v___x_3697_;
v_isShared_3701_ = v_isSharedCheck_3707_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_val_3698_);
lean_dec(v___x_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3707_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v_recArgPos_3702_; lean_object* v___x_3704_; 
v_recArgPos_3702_ = lean_ctor_get(v_val_3698_, 4);
lean_inc(v_recArgPos_3702_);
lean_dec(v_val_3698_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v_recArgPos_3702_);
v___x_3704_ = v___x_3700_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_recArgPos_3702_);
v___x_3704_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
}
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
lean_dec(v___x_3697_);
v___x_3708_ = lean_box(0);
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
return v___x_3709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3710_, v_a_3711_);
lean_dec(v_a_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_){
_start:
{
lean_object* v___x_3718_; 
lean_dec_ref(v_a_3715_);
v___x_3718_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3714_, v_a_3716_);
lean_dec(v_a_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = lean_get_structural_rec_arg_pos(v_declName_3719_, v_a_3720_, v_a_3721_);
return v_res_3723_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3781_ = lean_unsigned_to_nat(2295916746u);
v___x_3782_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3783_ = l_Lean_Name_num___override(v___x_3782_, v___x_3781_);
return v___x_3783_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3786_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3787_ = l_Lean_Name_str___override(v___x_3786_, v___x_3785_);
return v___x_3787_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3790_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3791_ = l_Lean_Name_str___override(v___x_3790_, v___x_3789_);
return v___x_3791_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = lean_unsigned_to_nat(2u);
v___x_3793_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3794_ = l_Lean_Name_num___override(v___x_3793_, v___x_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3797_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3796_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v___x_3798_; uint8_t v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec_ref_known(v___x_3797_, 1);
v___x_3798_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_3799_ = 0;
v___x_3800_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3801_ = l_Lean_registerTraceClass(v___x_3798_, v___x_3799_, v___x_3800_);
return v___x_3801_;
}
else
{
return v___x_3797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_3803_;
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
res = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_();
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
