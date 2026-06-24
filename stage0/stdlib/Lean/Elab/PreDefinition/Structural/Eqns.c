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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object*);
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
lean_object* v___x_228_; lean_object* v_env_229_; lean_object* v___x_230_; lean_object* v_mctx_231_; lean_object* v_lctx_232_; lean_object* v_options_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_228_ = lean_st_ref_get(v___y_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = lean_st_ref_get(v___y_224_);
v_mctx_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_mctx_231_);
lean_dec(v___x_230_);
v_lctx_232_ = lean_ctor_get(v___y_223_, 2);
v_options_233_ = lean_ctor_get(v___y_225_, 2);
lean_inc_ref(v_options_233_);
lean_inc_ref(v_lctx_232_);
v___x_234_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_234_, 0, v_env_229_);
lean_ctor_set(v___x_234_, 1, v_mctx_231_);
lean_ctor_set(v___x_234_, 2, v_lctx_232_);
lean_ctor_set(v___x_234_, 3, v_options_233_);
v___x_235_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set(v___x_235_, 1, v_msgData_222_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0___boxed(lean_object* v_msgData_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msgData_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_ref_250_; lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_ref_250_ = lean_ctor_get(v___y_247_, 5);
v___x_251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
lean_inc(v_ref_250_);
v___x_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_256_, 0, v_ref_250_);
lean_ctor_set(v___x_256_, 1, v_a_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg___boxed(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(lean_object* v_xs_268_, lean_object* v_x_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_array_get_size(v_xs_268_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1___boxed(lean_object* v_xs_277_, lean_object* v_x_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__1(v_xs_277_, v_x_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec_ref(v_x_278_);
lean_dec_ref(v_xs_277_);
return v_res_284_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0(void){
_start:
{
lean_object* v___x_285_; lean_object* v_dummy_286_; 
v___x_285_ = lean_box(0);
v_dummy_286_ = l_Lean_Expr_sort___override(v___x_285_);
return v_dummy_286_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__0));
v___x_289_ = l_Lean_stringToMessageData(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(lean_object* v_e_294_, lean_object* v_k_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___y_305_; lean_object* v___y_306_; lean_object* v___y_307_; lean_object* v___y_308_; 
if (lean_obj_tag(v_x_296_) == 5)
{
lean_object* v_fn_313_; lean_object* v_arg_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_fn_313_ = lean_ctor_get(v_x_296_, 0);
lean_inc_ref(v_fn_313_);
v_arg_314_ = lean_ctor_get(v_x_296_, 1);
lean_inc_ref(v_arg_314_);
lean_dec_ref_known(v_x_296_, 2);
v___x_315_ = lean_array_set(v_x_297_, v_x_298_, v_arg_314_);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_sub(v_x_298_, v___x_316_);
lean_dec(v_x_298_);
v_x_296_ = v_fn_313_;
v_x_297_ = v___x_315_;
v_x_298_ = v___x_317_;
goto _start;
}
else
{
lean_dec(v_x_298_);
if (lean_obj_tag(v_x_296_) == 11)
{
lean_object* v_typeName_319_; lean_object* v_idx_320_; lean_object* v_struct_321_; lean_object* v___f_322_; lean_object* v___x_323_; 
lean_dec_ref(v_e_294_);
v_typeName_319_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_typeName_319_);
v_idx_320_ = lean_ctor_get(v_x_296_, 1);
lean_inc(v_idx_320_);
v_struct_321_ = lean_ctor_get(v_x_296_, 2);
lean_inc_ref(v_struct_321_);
lean_dec_ref_known(v_x_296_, 3);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_322_, 0, v_typeName_319_);
lean_closure_set(v___f_322_, 1, v_idx_320_);
lean_closure_set(v___f_322_, 2, v_x_297_);
lean_closure_set(v___f_322_, 3, v_k_295_);
v___x_323_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_struct_321_, v___f_322_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_323_;
}
else
{
if (lean_obj_tag(v_x_296_) == 4)
{
lean_object* v_declName_324_; lean_object* v___x_325_; lean_object* v_env_326_; uint8_t v___x_327_; 
v_declName_324_ = lean_ctor_get(v_x_296_, 0);
v___x_325_ = lean_st_ref_get(v___y_302_);
v_env_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_env_326_);
lean_dec(v___x_325_);
lean_inc(v_declName_324_);
v___x_327_ = l_Lean_isBRecOnRecursor(v_env_326_, v_declName_324_);
if (v___x_327_ == 0)
{
lean_dec_ref_known(v_x_296_, 2);
lean_dec_ref(v_x_297_);
lean_dec_ref(v_k_295_);
v___y_305_ = v___y_299_;
v___y_306_ = v___y_300_;
v___y_307_ = v___y_301_;
v___y_308_ = v___y_302_;
goto v___jp_304_;
}
else
{
lean_object* v___x_328_; 
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc_ref(v_x_296_);
v___x_328_ = lean_infer_type(v_x_296_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___f_330_; uint8_t v___x_331_; lean_object* v___x_332_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
v___f_330_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2));
v___x_331_ = 0;
v___x_332_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_a_329_, v___f_330_, v___x_331_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref_known(v___x_332_, 1);
v___x_334_ = lean_array_get_size(v_x_297_);
v___x_335_ = lean_nat_dec_le(v_a_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_a_333_);
lean_dec_ref_known(v_x_296_, 2);
lean_dec_ref(v_x_297_);
lean_dec_ref(v_k_295_);
v___y_305_ = v___y_299_;
v___y_306_ = v___y_300_;
v___y_307_ = v___y_301_;
v___y_308_ = v___y_302_;
goto v___jp_304_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref(v_e_294_);
v___x_336_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_333_);
lean_inc_ref(v_x_297_);
v___x_337_ = l_Array_toSubarray___redArg(v_x_297_, v___x_336_, v_a_333_);
v___x_338_ = l_Subarray_copy___redArg(v___x_337_);
v___x_339_ = l_Lean_mkAppN(v_x_296_, v___x_338_);
lean_dec_ref(v___x_338_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v___y_299_);
lean_inc_ref(v___x_339_);
v___x_340_ = lean_infer_type(v___x_339_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = l_Array_toSubarray___redArg(v_x_297_, v_a_333_, v___x_334_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_343_, 0, v___x_342_);
lean_closure_set(v___f_343_, 1, v_k_295_);
lean_closure_set(v___f_343_, 2, v___x_339_);
v___x_344_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__4));
v___x_345_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v___x_344_, v_a_341_, v___f_343_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_345_;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v___x_339_);
lean_dec(v_a_333_);
lean_dec_ref(v_x_297_);
lean_dec_ref(v_k_295_);
v_a_346_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_340_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_340_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec_ref_known(v_x_296_, 2);
lean_dec_ref(v_x_297_);
lean_dec_ref(v_k_295_);
lean_dec_ref(v_e_294_);
v_a_354_ = lean_ctor_get(v___x_332_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_332_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_332_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref_known(v_x_296_, 2);
lean_dec_ref(v_x_297_);
lean_dec_ref(v_k_295_);
lean_dec_ref(v_e_294_);
v_a_362_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_328_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_328_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
else
{
lean_dec_ref(v_x_297_);
lean_dec_ref(v_x_296_);
lean_dec_ref(v_k_295_);
v___y_305_ = v___y_299_;
v___y_306_ = v___y_300_;
v___y_307_ = v___y_301_;
v___y_308_ = v___y_302_;
goto v___jp_304_;
}
}
}
v___jp_304_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__1);
v___x_310_ = l_Lean_indentExpr(v_e_294_);
v___x_311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_311_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v___x_312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(lean_object* v_e_370_, lean_object* v_k_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_dummy_377_; lean_object* v_nargs_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_dummy_377_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
v_nargs_378_ = l_Lean_Expr_getAppNumArgs(v_e_370_);
lean_inc(v_nargs_378_);
v___x_379_ = lean_mk_array(v_nargs_378_, v_dummy_377_);
v___x_380_ = lean_unsigned_to_nat(1u);
v___x_381_ = lean_nat_sub(v_nargs_378_, v___x_380_);
lean_dec(v_nargs_378_);
lean_inc_ref(v_e_370_);
v___x_382_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_370_, v_k_371_, v_e_370_, v___x_379_, v___x_381_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___boxed(lean_object* v_e_383_, lean_object* v_k_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_383_, v_k_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___boxed(lean_object* v_e_391_, lean_object* v_k_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_391_, v_k_392_, v_x_393_, v_x_394_, v_x_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(lean_object* v_00_u03b1_402_, lean_object* v_e_403_, lean_object* v_k_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v_e_403_, v_k_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___boxed(lean_object* v_00_u03b1_411_, lean_object* v_e_412_, lean_object* v_k_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go(v_00_u03b1_411_, v_e_412_, v_k_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(lean_object* v_00_u03b1_420_, lean_object* v_msg_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v_msg_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___boxed(lean_object* v_00_u03b1_428_, lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0(v_00_u03b1_428_, v_msg_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(lean_object* v_00_u03b1_436_, lean_object* v_name_437_, uint8_t v_bi_438_, lean_object* v_type_439_, lean_object* v_k_440_, uint8_t v_kind_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___redArg(v_name_437_, v_bi_438_, v_type_439_, v_k_440_, v_kind_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_448_, lean_object* v_name_449_, lean_object* v_bi_450_, lean_object* v_type_451_, lean_object* v_k_452_, lean_object* v_kind_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v_bi_boxed_459_; uint8_t v_kind_boxed_460_; lean_object* v_res_461_; 
v_bi_boxed_459_ = lean_unbox(v_bi_450_);
v_kind_boxed_460_ = lean_unbox(v_kind_453_);
v_res_461_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2_spec__3(v_00_u03b1_448_, v_name_449_, v_bi_boxed_459_, v_type_451_, v_k_452_, v_kind_boxed_460_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(lean_object* v_00_u03b1_462_, lean_object* v_name_463_, lean_object* v_type_464_, lean_object* v_k_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___redArg(v_name_463_, v_type_464_, v_k_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2___boxed(lean_object* v_00_u03b1_472_, lean_object* v_name_473_, lean_object* v_type_474_, lean_object* v_k_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__2(v_00_u03b1_472_, v_name_473_, v_type_474_, v_k_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(lean_object* v_00_u03b1_482_, lean_object* v_e_483_, lean_object* v_k_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg(v_e_483_, v_k_484_, v_x_485_, v_x_486_, v_x_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___boxed(lean_object* v_00_u03b1_494_, lean_object* v_e_495_, lean_object* v_k_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3(v_00_u03b1_494_, v_e_495_, v_k_496_, v_x_497_, v_x_498_, v_x_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(lean_object* v___x_506_, uint8_t v___x_507_, lean_object* v_brecOnApp_508_, lean_object* v_x_509_, lean_object* v_c_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_Meta_mkEq(v_c_510_, v___x_506_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v_a_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; 
v_a_517_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_516_, 1);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_518_);
v___x_520_ = lean_array_push(v___x_519_, v_x_509_);
v___x_521_ = 0;
v___x_522_ = 1;
v___x_523_ = l_Lean_Meta_mkLambdaFVars(v___x_520_, v_a_517_, v___x_521_, v___x_507_, v___x_521_, v___x_507_, v___x_522_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec_ref(v___x_520_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_brecOnApp_508_);
lean_ctor_set(v___x_528_, 1, v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_brecOnApp_508_);
v_a_533_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_523_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_523_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_x_509_);
lean_dec_ref(v_brecOnApp_508_);
v_a_541_ = lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_516_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_516_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed(lean_object* v___x_549_, lean_object* v___x_550_, lean_object* v_brecOnApp_551_, lean_object* v_x_552_, lean_object* v_c_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_652__boxed_559_; lean_object* v_res_560_; 
v___x_652__boxed_559_ = lean_unbox(v___x_550_);
v_res_560_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0(v___x_549_, v___x_652__boxed_559_, v_brecOnApp_551_, v_x_552_, v_c_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_560_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__2));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(lean_object* v_goal_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_574_ = lean_unsigned_to_nat(3u);
v___x_575_ = l_Lean_Expr_isAppOfArity(v_goal_567_, v___x_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__3);
v___x_577_ = l_Lean_indentExpr(v_goal_567_);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_578_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; 
v___x_580_ = l_Lean_Expr_appFn_x21(v_goal_567_);
v___x_581_ = l_Lean_Expr_appArg_x21(v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_Lean_Expr_appArg_x21(v_goal_567_);
lean_dec_ref(v_goal_567_);
v___x_583_ = lean_box(v___x_575_);
v___f_584_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___lam__0___boxed), 10, 2);
lean_closure_set(v___f_584_, 0, v___x_582_);
lean_closure_set(v___f_584_, 1, v___x_583_);
v___x_585_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg(v___x_581_, v___f_584_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___boxed(lean_object* v_goal_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_goal_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
lean_dec(v_a_588_);
lean_dec_ref(v_a_587_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(lean_object* v_mvarId_593_, lean_object* v_x_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_593_, v_x_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_a_609_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_600_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_600_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_617_, lean_object* v_x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_617_, v_x_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(lean_object* v_00_u03b1_625_, lean_object* v_mvarId_626_, lean_object* v_x_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_626_, v_x_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___boxed(lean_object* v_00_u03b1_634_, lean_object* v_mvarId_635_, lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0(v_00_u03b1_634_, v_mvarId_635_, v_x_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_642_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(lean_object* v_declName_643_, lean_object* v_x_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = lean_name_eq(v_x_644_, v_declName_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed(lean_object* v_declName_646_, lean_object* v_x_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0(v_declName_646_, v_x_647_);
lean_dec(v_x_647_);
lean_dec(v_declName_646_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(lean_object* v_mvarId_650_, lean_object* v___f_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v___x_657_; 
lean_inc(v_mvarId_650_);
v___x_657_ = l_Lean_MVarId_getType_x27(v_mvarId_650_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_727_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_727_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_727_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_727_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_663_ = lean_unsigned_to_nat(3u);
v___x_664_ = l_Lean_Expr_isAppOfArity(v_a_658_, v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_667_; 
lean_dec(v_a_658_);
lean_dec_ref(v___f_651_);
lean_dec(v_mvarId_650_);
v___x_665_ = lean_box(0);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_665_);
v___x_667_ = v___x_660_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
lean_del_object(v___x_660_);
v___x_669_ = l_Lean_Expr_appArg_x21(v_a_658_);
v___x_670_ = l_Lean_Expr_consumeMData(v___x_669_);
lean_dec_ref(v___x_669_);
v___x_671_ = 0;
v___x_672_ = l_Lean_Meta_delta_x3f(v___x_670_, v___f_651_, v___x_671_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_718_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_718_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_718_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_718_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
if (lean_obj_tag(v_a_673_) == 1)
{
lean_object* v_val_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_713_; 
lean_del_object(v___x_675_);
v_val_677_ = lean_ctor_get(v_a_673_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_713_ == 0)
{
v___x_679_ = v_a_673_;
v_isShared_680_ = v_isSharedCheck_713_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_val_677_);
lean_dec(v_a_673_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_713_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = l_Lean_Expr_appFn_x21(v_a_658_);
lean_dec(v_a_658_);
v___x_682_ = l_Lean_Expr_appArg_x21(v___x_681_);
lean_dec_ref(v___x_681_);
v___x_683_ = l_Lean_Meta_mkEq(v___x_682_, v_val_677_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v___x_685_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_650_, v_a_684_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_696_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_696_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v_a_686_);
v___x_691_ = v___x_679_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
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
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_del_object(v___x_679_);
v_a_697_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_685_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_685_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_679_);
lean_dec(v_mvarId_650_);
v_a_705_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_683_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_683_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_a_673_);
lean_dec(v_a_658_);
lean_dec(v_mvarId_650_);
v___x_714_ = lean_box(0);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_714_);
v___x_716_ = v___x_675_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_658_);
lean_dec(v_mvarId_650_);
v_a_719_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_672_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_672_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec_ref(v___f_651_);
lean_dec(v_mvarId_650_);
v_a_728_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_657_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_657_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed(lean_object* v_mvarId_736_, lean_object* v___f_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1(v_mvarId_736_, v___f_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(lean_object* v_mvarId_744_, lean_object* v_declName_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___f_751_; lean_object* v___f_752_; lean_object* v___x_753_; 
v___f_751_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_751_, 0, v_declName_745_);
lean_inc(v_mvarId_744_);
v___f_752_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___lam__1___boxed), 7, 2);
lean_closure_set(v___f_752_, 0, v_mvarId_744_);
lean_closure_set(v___f_752_, 1, v___f_751_);
v___x_753_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_744_, v___f_752_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f___boxed(lean_object* v_mvarId_754_, lean_object* v_declName_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_754_, v_declName_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_761_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(32u);
v___x_763_ = lean_mk_empty_array_with_capacity(v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_765_ = ((size_t)5ULL);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_unsigned_to_nat(32u);
v___x_768_ = lean_mk_empty_array_with_capacity(v___x_767_);
v___x_769_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__0);
v___x_770_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
lean_ctor_set(v___x_770_, 2, v___x_766_);
lean_ctor_set(v___x_770_, 3, v___x_766_);
lean_ctor_set_usize(v___x_770_, 4, v___x_765_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(lean_object* v___y_771_){
_start:
{
lean_object* v___x_773_; lean_object* v_traceState_774_; lean_object* v_traces_775_; lean_object* v___x_776_; lean_object* v_traceState_777_; lean_object* v_env_778_; lean_object* v_nextMacroScope_779_; lean_object* v_ngen_780_; lean_object* v_auxDeclNGen_781_; lean_object* v_cache_782_; lean_object* v_messages_783_; lean_object* v_infoState_784_; lean_object* v_snapshotTasks_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_804_; 
v___x_773_ = lean_st_ref_get(v___y_771_);
v_traceState_774_ = lean_ctor_get(v___x_773_, 4);
lean_inc_ref(v_traceState_774_);
lean_dec(v___x_773_);
v_traces_775_ = lean_ctor_get(v_traceState_774_, 0);
lean_inc_ref(v_traces_775_);
lean_dec_ref(v_traceState_774_);
v___x_776_ = lean_st_ref_take(v___y_771_);
v_traceState_777_ = lean_ctor_get(v___x_776_, 4);
v_env_778_ = lean_ctor_get(v___x_776_, 0);
v_nextMacroScope_779_ = lean_ctor_get(v___x_776_, 1);
v_ngen_780_ = lean_ctor_get(v___x_776_, 2);
v_auxDeclNGen_781_ = lean_ctor_get(v___x_776_, 3);
v_cache_782_ = lean_ctor_get(v___x_776_, 5);
v_messages_783_ = lean_ctor_get(v___x_776_, 6);
v_infoState_784_ = lean_ctor_get(v___x_776_, 7);
v_snapshotTasks_785_ = lean_ctor_get(v___x_776_, 8);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_804_ == 0)
{
v___x_787_ = v___x_776_;
v_isShared_788_ = v_isSharedCheck_804_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snapshotTasks_785_);
lean_inc(v_infoState_784_);
lean_inc(v_messages_783_);
lean_inc(v_cache_782_);
lean_inc(v_traceState_777_);
lean_inc(v_auxDeclNGen_781_);
lean_inc(v_ngen_780_);
lean_inc(v_nextMacroScope_779_);
lean_inc(v_env_778_);
lean_dec(v___x_776_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_804_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
uint64_t v_tid_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_802_; 
v_tid_789_ = lean_ctor_get_uint64(v_traceState_777_, sizeof(void*)*1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_traceState_777_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v_traceState_777_, 0);
lean_dec(v_unused_803_);
v___x_791_ = v_traceState_777_;
v_isShared_792_ = v_isSharedCheck_802_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_traceState_777_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_802_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_793_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___closed__1);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_793_);
v___x_795_ = v___x_791_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_793_);
lean_ctor_set_uint64(v_reuseFailAlloc_801_, sizeof(void*)*1, v_tid_789_);
v___x_795_ = v_reuseFailAlloc_801_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 4, v___x_795_);
v___x_797_ = v___x_787_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_env_778_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v_nextMacroScope_779_);
lean_ctor_set(v_reuseFailAlloc_800_, 2, v_ngen_780_);
lean_ctor_set(v_reuseFailAlloc_800_, 3, v_auxDeclNGen_781_);
lean_ctor_set(v_reuseFailAlloc_800_, 4, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_800_, 5, v_cache_782_);
lean_ctor_set(v_reuseFailAlloc_800_, 6, v_messages_783_);
lean_ctor_set(v_reuseFailAlloc_800_, 7, v_infoState_784_);
lean_ctor_set(v_reuseFailAlloc_800_, 8, v_snapshotTasks_785_);
v___x_797_ = v_reuseFailAlloc_800_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_st_ref_set(v___y_771_, v___x_797_);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v_traces_775_);
return v___x_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg___boxed(lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_805_);
lean_dec(v___y_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v___y_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v_opts_820_, lean_object* v_opt_821_){
_start:
{
lean_object* v_name_822_; lean_object* v_defValue_823_; lean_object* v_map_824_; lean_object* v___x_825_; 
v_name_822_ = lean_ctor_get(v_opt_821_, 0);
v_defValue_823_ = lean_ctor_get(v_opt_821_, 1);
v_map_824_ = lean_ctor_get(v_opts_820_, 0);
v___x_825_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_824_, v_name_822_);
if (lean_obj_tag(v___x_825_) == 0)
{
uint8_t v___x_826_; 
v___x_826_ = lean_unbox(v_defValue_823_);
return v___x_826_;
}
else
{
lean_object* v_val_827_; 
v_val_827_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v___x_825_, 1);
if (lean_obj_tag(v_val_827_) == 1)
{
uint8_t v_v_828_; 
v_v_828_ = lean_ctor_get_uint8(v_val_827_, 0);
lean_dec_ref_known(v_val_827_, 0);
return v_v_828_;
}
else
{
uint8_t v___x_829_; 
lean_dec(v_val_827_);
v___x_829_ = lean_unbox(v_defValue_823_);
return v___x_829_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v_opts_830_, lean_object* v_opt_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_830_, v_opt_831_);
lean_dec_ref(v_opt_831_);
lean_dec_ref(v_opts_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0));
v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object* v_mvarId_837_, lean_object* v_x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_844_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1);
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v_mvarId_837_);
v___x_846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object* v_mvarId_848_, lean_object* v_x_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(v_mvarId_848_, v_x_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec_ref(v_x_849_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object* v_____r_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_box(0);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object* v_____r_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_____r_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
return v_res_870_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0(void){
_start:
{
lean_object* v___x_871_; double v___x_872_; 
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_float_of_nat(v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v_cls_876_, lean_object* v_msg_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_ref_883_; lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_929_; 
v_ref_883_ = lean_ctor_get(v___y_880_, 5);
v___x_884_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_929_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_929_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_929_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v_traceState_890_; lean_object* v_env_891_; lean_object* v_nextMacroScope_892_; lean_object* v_ngen_893_; lean_object* v_auxDeclNGen_894_; lean_object* v_cache_895_; lean_object* v_messages_896_; lean_object* v_infoState_897_; lean_object* v_snapshotTasks_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_928_; 
v___x_889_ = lean_st_ref_take(v___y_881_);
v_traceState_890_ = lean_ctor_get(v___x_889_, 4);
v_env_891_ = lean_ctor_get(v___x_889_, 0);
v_nextMacroScope_892_ = lean_ctor_get(v___x_889_, 1);
v_ngen_893_ = lean_ctor_get(v___x_889_, 2);
v_auxDeclNGen_894_ = lean_ctor_get(v___x_889_, 3);
v_cache_895_ = lean_ctor_get(v___x_889_, 5);
v_messages_896_ = lean_ctor_get(v___x_889_, 6);
v_infoState_897_ = lean_ctor_get(v___x_889_, 7);
v_snapshotTasks_898_ = lean_ctor_get(v___x_889_, 8);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_928_ == 0)
{
v___x_900_ = v___x_889_;
v_isShared_901_ = v_isSharedCheck_928_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_snapshotTasks_898_);
lean_inc(v_infoState_897_);
lean_inc(v_messages_896_);
lean_inc(v_cache_895_);
lean_inc(v_traceState_890_);
lean_inc(v_auxDeclNGen_894_);
lean_inc(v_ngen_893_);
lean_inc(v_nextMacroScope_892_);
lean_inc(v_env_891_);
lean_dec(v___x_889_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_928_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
uint64_t v_tid_902_; lean_object* v_traces_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_927_; 
v_tid_902_ = lean_ctor_get_uint64(v_traceState_890_, sizeof(void*)*1);
v_traces_903_ = lean_ctor_get(v_traceState_890_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v_traceState_890_);
if (v_isSharedCheck_927_ == 0)
{
v___x_905_ = v_traceState_890_;
v_isShared_906_ = v_isSharedCheck_927_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_traces_903_);
lean_dec(v_traceState_890_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_927_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; double v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___x_907_ = lean_box(0);
v___x_908_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
v___x_909_ = 0;
v___x_910_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_911_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_911_, 0, v_cls_876_);
lean_ctor_set(v___x_911_, 1, v___x_907_);
lean_ctor_set(v___x_911_, 2, v___x_910_);
lean_ctor_set_float(v___x_911_, sizeof(void*)*3, v___x_908_);
lean_ctor_set_float(v___x_911_, sizeof(void*)*3 + 8, v___x_908_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*3 + 16, v___x_909_);
v___x_912_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2));
v___x_913_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v_a_885_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
lean_inc(v_ref_883_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_ref_883_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_PersistentArray_push___redArg(v_traces_903_, v___x_914_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_915_);
v___x_917_ = v___x_905_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_915_);
lean_ctor_set_uint64(v_reuseFailAlloc_926_, sizeof(void*)*1, v_tid_902_);
v___x_917_ = v_reuseFailAlloc_926_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 4, v___x_917_);
v___x_919_ = v___x_900_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_env_891_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_nextMacroScope_892_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v_ngen_893_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v_auxDeclNGen_894_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_925_, 5, v_cache_895_);
lean_ctor_set(v_reuseFailAlloc_925_, 6, v_messages_896_);
lean_ctor_set(v_reuseFailAlloc_925_, 7, v_infoState_897_);
lean_ctor_set(v_reuseFailAlloc_925_, 8, v_snapshotTasks_898_);
v___x_919_ = v_reuseFailAlloc_925_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_920_ = lean_st_ref_set(v___y_881_, v___x_919_);
v___x_921_ = lean_box(0);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_921_);
v___x_923_ = v___x_887_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_930_, lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_930_, v_msg_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(lean_object* v_opts_938_, lean_object* v_opt_939_){
_start:
{
lean_object* v_name_940_; lean_object* v_defValue_941_; lean_object* v_map_942_; lean_object* v___x_943_; 
v_name_940_ = lean_ctor_get(v_opt_939_, 0);
v_defValue_941_ = lean_ctor_get(v_opt_939_, 1);
v_map_942_ = lean_ctor_get(v_opts_938_, 0);
v___x_943_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_942_, v_name_940_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_inc(v_defValue_941_);
return v_defValue_941_;
}
else
{
lean_object* v_val_944_; 
v_val_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_val_944_);
lean_dec_ref_known(v___x_943_, 1);
if (lean_obj_tag(v_val_944_) == 3)
{
lean_object* v_v_945_; 
v_v_945_ = lean_ctor_get(v_val_944_, 0);
lean_inc(v_v_945_);
lean_dec_ref_known(v_val_944_, 1);
return v_v_945_;
}
else
{
lean_dec(v_val_944_);
lean_inc(v_defValue_941_);
return v_defValue_941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8___boxed(lean_object* v_opts_946_, lean_object* v_opt_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_946_, v_opt_947_);
lean_dec_ref(v_opt_947_);
lean_dec_ref(v_opts_946_);
return v_res_948_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object* v_e_949_){
_start:
{
if (lean_obj_tag(v_e_949_) == 0)
{
uint8_t v___x_950_; 
v___x_950_ = 2;
return v___x_950_;
}
else
{
uint8_t v___x_951_; 
v___x_951_ = 0;
return v___x_951_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object* v_e_952_){
_start:
{
uint8_t v_res_953_; lean_object* v_r_954_; 
v_res_953_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_e_952_);
lean_dec_ref(v_e_952_);
v_r_954_ = lean_box(v_res_953_);
return v_r_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(size_t v_sz_955_, size_t v_i_956_, lean_object* v_bs_957_){
_start:
{
uint8_t v___x_958_; 
v___x_958_ = lean_usize_dec_lt(v_i_956_, v_sz_955_);
if (v___x_958_ == 0)
{
return v_bs_957_;
}
else
{
lean_object* v_v_959_; lean_object* v_msg_960_; lean_object* v___x_961_; lean_object* v_bs_x27_962_; size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v_v_959_ = lean_array_uget_borrowed(v_bs_957_, v_i_956_);
v_msg_960_ = lean_ctor_get(v_v_959_, 1);
lean_inc_ref(v_msg_960_);
v___x_961_ = lean_unsigned_to_nat(0u);
v_bs_x27_962_ = lean_array_uset(v_bs_957_, v_i_956_, v___x_961_);
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_956_, v___x_963_);
v___x_965_ = lean_array_uset(v_bs_x27_962_, v_i_956_, v_msg_960_);
v_i_956_ = v___x_964_;
v_bs_957_ = v___x_965_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6___boxed(lean_object* v_sz_967_, lean_object* v_i_968_, lean_object* v_bs_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_967_);
lean_dec(v_sz_967_);
v_i_boxed_971_ = lean_unbox_usize(v_i_968_);
lean_dec(v_i_968_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_boxed_970_, v_i_boxed_971_, v_bs_969_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object* v_oldTraces_973_, lean_object* v_data_974_, lean_object* v_ref_975_, lean_object* v_msg_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v_fileName_982_; lean_object* v_fileMap_983_; lean_object* v_options_984_; lean_object* v_currRecDepth_985_; lean_object* v_maxRecDepth_986_; lean_object* v_ref_987_; lean_object* v_currNamespace_988_; lean_object* v_openDecls_989_; lean_object* v_initHeartbeats_990_; lean_object* v_maxHeartbeats_991_; lean_object* v_quotContext_992_; lean_object* v_currMacroScope_993_; uint8_t v_diag_994_; lean_object* v_cancelTk_x3f_995_; uint8_t v_suppressElabErrors_996_; lean_object* v_inheritedTraceOptions_997_; lean_object* v___x_998_; lean_object* v_traceState_999_; lean_object* v_traces_1000_; lean_object* v_ref_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; size_t v_sz_1004_; size_t v___x_1005_; lean_object* v___x_1006_; lean_object* v_msg_1007_; lean_object* v___x_1008_; lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1046_; 
v_fileName_982_ = lean_ctor_get(v___y_979_, 0);
v_fileMap_983_ = lean_ctor_get(v___y_979_, 1);
v_options_984_ = lean_ctor_get(v___y_979_, 2);
v_currRecDepth_985_ = lean_ctor_get(v___y_979_, 3);
v_maxRecDepth_986_ = lean_ctor_get(v___y_979_, 4);
v_ref_987_ = lean_ctor_get(v___y_979_, 5);
v_currNamespace_988_ = lean_ctor_get(v___y_979_, 6);
v_openDecls_989_ = lean_ctor_get(v___y_979_, 7);
v_initHeartbeats_990_ = lean_ctor_get(v___y_979_, 8);
v_maxHeartbeats_991_ = lean_ctor_get(v___y_979_, 9);
v_quotContext_992_ = lean_ctor_get(v___y_979_, 10);
v_currMacroScope_993_ = lean_ctor_get(v___y_979_, 11);
v_diag_994_ = lean_ctor_get_uint8(v___y_979_, sizeof(void*)*14);
v_cancelTk_x3f_995_ = lean_ctor_get(v___y_979_, 12);
v_suppressElabErrors_996_ = lean_ctor_get_uint8(v___y_979_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_997_ = lean_ctor_get(v___y_979_, 13);
v___x_998_ = lean_st_ref_get(v___y_980_);
v_traceState_999_ = lean_ctor_get(v___x_998_, 4);
lean_inc_ref(v_traceState_999_);
lean_dec(v___x_998_);
v_traces_1000_ = lean_ctor_get(v_traceState_999_, 0);
lean_inc_ref(v_traces_1000_);
lean_dec_ref(v_traceState_999_);
v_ref_1001_ = l_Lean_replaceRef(v_ref_975_, v_ref_987_);
lean_inc_ref(v_inheritedTraceOptions_997_);
lean_inc(v_cancelTk_x3f_995_);
lean_inc(v_currMacroScope_993_);
lean_inc(v_quotContext_992_);
lean_inc(v_maxHeartbeats_991_);
lean_inc(v_initHeartbeats_990_);
lean_inc(v_openDecls_989_);
lean_inc(v_currNamespace_988_);
lean_inc(v_maxRecDepth_986_);
lean_inc(v_currRecDepth_985_);
lean_inc_ref(v_options_984_);
lean_inc_ref(v_fileMap_983_);
lean_inc_ref(v_fileName_982_);
v___x_1002_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1002_, 0, v_fileName_982_);
lean_ctor_set(v___x_1002_, 1, v_fileMap_983_);
lean_ctor_set(v___x_1002_, 2, v_options_984_);
lean_ctor_set(v___x_1002_, 3, v_currRecDepth_985_);
lean_ctor_set(v___x_1002_, 4, v_maxRecDepth_986_);
lean_ctor_set(v___x_1002_, 5, v_ref_1001_);
lean_ctor_set(v___x_1002_, 6, v_currNamespace_988_);
lean_ctor_set(v___x_1002_, 7, v_openDecls_989_);
lean_ctor_set(v___x_1002_, 8, v_initHeartbeats_990_);
lean_ctor_set(v___x_1002_, 9, v_maxHeartbeats_991_);
lean_ctor_set(v___x_1002_, 10, v_quotContext_992_);
lean_ctor_set(v___x_1002_, 11, v_currMacroScope_993_);
lean_ctor_set(v___x_1002_, 12, v_cancelTk_x3f_995_);
lean_ctor_set(v___x_1002_, 13, v_inheritedTraceOptions_997_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*14, v_diag_994_);
lean_ctor_set_uint8(v___x_1002_, sizeof(void*)*14 + 1, v_suppressElabErrors_996_);
v___x_1003_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1000_);
lean_dec_ref(v_traces_1000_);
v_sz_1004_ = lean_array_size(v___x_1003_);
v___x_1005_ = ((size_t)0ULL);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5_spec__6(v_sz_1004_, v___x_1005_, v___x_1003_);
v_msg_1007_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1007_, 0, v_data_974_);
lean_ctor_set(v_msg_1007_, 1, v_msg_976_);
lean_ctor_set(v_msg_1007_, 2, v___x_1006_);
v___x_1008_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_1007_, v___y_977_, v___y_978_, v___x_1002_, v___y_980_);
lean_dec_ref_known(v___x_1002_, 14);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1046_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1046_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v_traceState_1014_; lean_object* v_env_1015_; lean_object* v_nextMacroScope_1016_; lean_object* v_ngen_1017_; lean_object* v_auxDeclNGen_1018_; lean_object* v_cache_1019_; lean_object* v_messages_1020_; lean_object* v_infoState_1021_; lean_object* v_snapshotTasks_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1045_; 
v___x_1013_ = lean_st_ref_take(v___y_980_);
v_traceState_1014_ = lean_ctor_get(v___x_1013_, 4);
v_env_1015_ = lean_ctor_get(v___x_1013_, 0);
v_nextMacroScope_1016_ = lean_ctor_get(v___x_1013_, 1);
v_ngen_1017_ = lean_ctor_get(v___x_1013_, 2);
v_auxDeclNGen_1018_ = lean_ctor_get(v___x_1013_, 3);
v_cache_1019_ = lean_ctor_get(v___x_1013_, 5);
v_messages_1020_ = lean_ctor_get(v___x_1013_, 6);
v_infoState_1021_ = lean_ctor_get(v___x_1013_, 7);
v_snapshotTasks_1022_ = lean_ctor_get(v___x_1013_, 8);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1024_ = v___x_1013_;
v_isShared_1025_ = v_isSharedCheck_1045_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_snapshotTasks_1022_);
lean_inc(v_infoState_1021_);
lean_inc(v_messages_1020_);
lean_inc(v_cache_1019_);
lean_inc(v_traceState_1014_);
lean_inc(v_auxDeclNGen_1018_);
lean_inc(v_ngen_1017_);
lean_inc(v_nextMacroScope_1016_);
lean_inc(v_env_1015_);
lean_dec(v___x_1013_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1045_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
uint64_t v_tid_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1043_; 
v_tid_1026_ = lean_ctor_get_uint64(v_traceState_1014_, sizeof(void*)*1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_traceState_1014_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_traceState_1014_, 0);
lean_dec(v_unused_1044_);
v___x_1028_ = v_traceState_1014_;
v_isShared_1029_ = v_isSharedCheck_1043_;
goto v_resetjp_1027_;
}
else
{
lean_dec(v_traceState_1014_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1043_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_ref_975_);
lean_ctor_set(v___x_1030_, 1, v_a_1009_);
v___x_1031_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_973_, v___x_1030_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1031_);
v___x_1033_ = v___x_1028_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1031_);
lean_ctor_set_uint64(v_reuseFailAlloc_1042_, sizeof(void*)*1, v_tid_1026_);
v___x_1033_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v___x_1033_);
v___x_1035_ = v___x_1024_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_env_1015_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_nextMacroScope_1016_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_ngen_1017_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_auxDeclNGen_1018_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1041_, 5, v_cache_1019_);
lean_ctor_set(v_reuseFailAlloc_1041_, 6, v_messages_1020_);
lean_ctor_set(v_reuseFailAlloc_1041_, 7, v_infoState_1021_);
lean_ctor_set(v_reuseFailAlloc_1041_, 8, v_snapshotTasks_1022_);
v___x_1035_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1036_ = lean_st_ref_set(v___y_980_, v___x_1035_);
v___x_1037_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1037_);
v___x_1039_ = v___x_1011_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object* v_oldTraces_1047_, lean_object* v_data_1048_, lean_object* v_ref_1049_, lean_object* v_msg_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1047_, v_data_1048_, v_ref_1049_, v_msg_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(lean_object* v_x_1057_){
_start:
{
if (lean_obj_tag(v_x_1057_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
v_a_1059_ = lean_ctor_get(v_x_1057_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_1057_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v_x_1057_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v_x_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 1);
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
v_a_1067_ = lean_ctor_get(v_x_1057_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_x_1057_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v_x_1057_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v_x_1057_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 0);
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg___boxed(lean_object* v_x_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_1075_);
return v_res_1077_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2(void){
_start:
{
lean_object* v___x_1081_; double v___x_1082_; 
v___x_1081_ = lean_unsigned_to_nat(1000u);
v___x_1082_ = lean_float_of_nat(v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_cls_1083_, uint8_t v_collapsed_1084_, lean_object* v_tag_1085_, lean_object* v_opts_1086_, uint8_t v_clsEnabled_1087_, lean_object* v_oldTraces_1088_, lean_object* v_msg_1089_, lean_object* v_resStartStop_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v_data_1101_; lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; lean_object* v___y_1109_; lean_object* v_a_1110_; uint8_t v___y_1125_; double v___y_1156_; 
v_fst_1096_ = lean_ctor_get(v_resStartStop_1090_, 0);
lean_inc(v_fst_1096_);
v_snd_1097_ = lean_ctor_get(v_resStartStop_1090_, 1);
lean_inc(v_snd_1097_);
lean_dec_ref(v_resStartStop_1090_);
v_fst_1104_ = lean_ctor_get(v_snd_1097_, 0);
lean_inc(v_fst_1104_);
v_snd_1105_ = lean_ctor_get(v_snd_1097_, 1);
lean_inc(v_snd_1105_);
lean_dec(v_snd_1097_);
v___x_1106_ = l_Lean_trace_profiler;
v___x_1107_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1086_, v___x_1106_);
if (v___x_1107_ == 0)
{
v___y_1125_ = v___x_1107_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1162_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1086_, v___x_1161_);
if (v___x_1162_ == 0)
{
lean_object* v___x_1163_; lean_object* v___x_1164_; double v___x_1165_; double v___x_1166_; double v___x_1167_; 
v___x_1163_ = l_Lean_trace_profiler_threshold;
v___x_1164_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1086_, v___x_1163_);
v___x_1165_ = lean_float_of_nat(v___x_1164_);
v___x_1166_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_1167_ = lean_float_div(v___x_1165_, v___x_1166_);
v___y_1156_ = v___x_1167_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; double v___x_1170_; 
v___x_1168_ = l_Lean_trace_profiler_threshold;
v___x_1169_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1086_, v___x_1168_);
v___x_1170_ = lean_float_of_nat(v___x_1169_);
v___y_1156_ = v___x_1170_;
goto v___jp_1155_;
}
}
v___jp_1098_:
{
lean_object* v___x_1102_; 
lean_inc(v___y_1099_);
v___x_1102_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_1088_, v_data_1101_, v___y_1099_, v___y_1100_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v___x_1103_; 
lean_dec_ref_known(v___x_1102_, 1);
v___x_1103_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1096_);
return v___x_1103_;
}
else
{
lean_dec(v_fst_1096_);
return v___x_1102_;
}
}
v___jp_1108_:
{
uint8_t v_result_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; double v___x_1114_; lean_object* v_data_1115_; 
v_result_1111_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_fst_1096_);
v___x_1112_ = lean_box(v_result_1111_);
v___x_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
v___x_1114_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_1085_);
lean_inc_ref(v___x_1113_);
lean_inc(v_cls_1083_);
v_data_1115_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1115_, 0, v_cls_1083_);
lean_ctor_set(v_data_1115_, 1, v___x_1113_);
lean_ctor_set(v_data_1115_, 2, v_tag_1085_);
lean_ctor_set_float(v_data_1115_, sizeof(void*)*3, v___x_1114_);
lean_ctor_set_float(v_data_1115_, sizeof(void*)*3 + 8, v___x_1114_);
lean_ctor_set_uint8(v_data_1115_, sizeof(void*)*3 + 16, v_collapsed_1084_);
if (v___x_1107_ == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
lean_dec(v_snd_1105_);
lean_dec(v_fst_1104_);
lean_dec_ref(v_tag_1085_);
lean_dec(v_cls_1083_);
v___y_1099_ = v___y_1109_;
v___y_1100_ = v_a_1110_;
v_data_1101_ = v_data_1115_;
goto v___jp_1098_;
}
else
{
lean_object* v_data_1116_; double v___x_1117_; double v___x_1118_; 
lean_dec_ref_known(v_data_1115_, 3);
v_data_1116_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1116_, 0, v_cls_1083_);
lean_ctor_set(v_data_1116_, 1, v___x_1113_);
lean_ctor_set(v_data_1116_, 2, v_tag_1085_);
v___x_1117_ = lean_unbox_float(v_fst_1104_);
lean_dec(v_fst_1104_);
lean_ctor_set_float(v_data_1116_, sizeof(void*)*3, v___x_1117_);
v___x_1118_ = lean_unbox_float(v_snd_1105_);
lean_dec(v_snd_1105_);
lean_ctor_set_float(v_data_1116_, sizeof(void*)*3 + 8, v___x_1118_);
lean_ctor_set_uint8(v_data_1116_, sizeof(void*)*3 + 16, v_collapsed_1084_);
v___y_1099_ = v___y_1109_;
v___y_1100_ = v_a_1110_;
v_data_1101_ = v_data_1116_;
goto v___jp_1098_;
}
}
v___jp_1119_:
{
lean_object* v_ref_1120_; lean_object* v___x_1121_; 
v_ref_1120_ = lean_ctor_get(v___y_1093_, 5);
lean_inc(v___y_1094_);
lean_inc_ref(v___y_1093_);
lean_inc(v___y_1092_);
lean_inc_ref(v___y_1091_);
lean_inc(v_fst_1096_);
v___x_1121_ = lean_apply_6(v_msg_1089_, v_fst_1096_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, lean_box(0));
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
lean_dec_ref_known(v___x_1121_, 1);
v___y_1109_ = v_ref_1120_;
v_a_1110_ = v_a_1122_;
goto v___jp_1108_;
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref_known(v___x_1121_, 1);
v___x_1123_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_1109_ = v_ref_1120_;
v_a_1110_ = v___x_1123_;
goto v___jp_1108_;
}
}
v___jp_1124_:
{
if (v_clsEnabled_1087_ == 0)
{
if (v___y_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v_traceState_1127_; lean_object* v_env_1128_; lean_object* v_nextMacroScope_1129_; lean_object* v_ngen_1130_; lean_object* v_auxDeclNGen_1131_; lean_object* v_cache_1132_; lean_object* v_messages_1133_; lean_object* v_infoState_1134_; lean_object* v_snapshotTasks_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_snd_1105_);
lean_dec(v_fst_1104_);
lean_dec_ref(v_msg_1089_);
lean_dec_ref(v_tag_1085_);
lean_dec(v_cls_1083_);
v___x_1126_ = lean_st_ref_take(v___y_1094_);
v_traceState_1127_ = lean_ctor_get(v___x_1126_, 4);
v_env_1128_ = lean_ctor_get(v___x_1126_, 0);
v_nextMacroScope_1129_ = lean_ctor_get(v___x_1126_, 1);
v_ngen_1130_ = lean_ctor_get(v___x_1126_, 2);
v_auxDeclNGen_1131_ = lean_ctor_get(v___x_1126_, 3);
v_cache_1132_ = lean_ctor_get(v___x_1126_, 5);
v_messages_1133_ = lean_ctor_get(v___x_1126_, 6);
v_infoState_1134_ = lean_ctor_get(v___x_1126_, 7);
v_snapshotTasks_1135_ = lean_ctor_get(v___x_1126_, 8);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1137_ = v___x_1126_;
v_isShared_1138_ = v_isSharedCheck_1154_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snapshotTasks_1135_);
lean_inc(v_infoState_1134_);
lean_inc(v_messages_1133_);
lean_inc(v_cache_1132_);
lean_inc(v_traceState_1127_);
lean_inc(v_auxDeclNGen_1131_);
lean_inc(v_ngen_1130_);
lean_inc(v_nextMacroScope_1129_);
lean_inc(v_env_1128_);
lean_dec(v___x_1126_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1154_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint64_t v_tid_1139_; lean_object* v_traces_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1153_; 
v_tid_1139_ = lean_ctor_get_uint64(v_traceState_1127_, sizeof(void*)*1);
v_traces_1140_ = lean_ctor_get(v_traceState_1127_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_traceState_1127_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1142_ = v_traceState_1127_;
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_traces_1140_);
lean_dec(v_traceState_1127_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1153_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1144_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1088_, v_traces_1140_);
lean_dec_ref(v_traces_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1146_ = v___x_1142_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1144_);
lean_ctor_set_uint64(v_reuseFailAlloc_1152_, sizeof(void*)*1, v_tid_1139_);
v___x_1146_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
lean_object* v___x_1148_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 4, v___x_1146_);
v___x_1148_ = v___x_1137_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_env_1128_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_nextMacroScope_1129_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_ngen_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_auxDeclNGen_1131_);
lean_ctor_set(v_reuseFailAlloc_1151_, 4, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1151_, 5, v_cache_1132_);
lean_ctor_set(v_reuseFailAlloc_1151_, 6, v_messages_1133_);
lean_ctor_set(v_reuseFailAlloc_1151_, 7, v_infoState_1134_);
lean_ctor_set(v_reuseFailAlloc_1151_, 8, v_snapshotTasks_1135_);
v___x_1148_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = lean_st_ref_set(v___y_1094_, v___x_1148_);
v___x_1150_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_1096_);
return v___x_1150_;
}
}
}
}
}
else
{
goto v___jp_1119_;
}
}
else
{
goto v___jp_1119_;
}
}
v___jp_1155_:
{
double v___x_1157_; double v___x_1158_; double v___x_1159_; uint8_t v___x_1160_; 
v___x_1157_ = lean_unbox_float(v_snd_1105_);
v___x_1158_ = lean_unbox_float(v_fst_1104_);
v___x_1159_ = lean_float_sub(v___x_1157_, v___x_1158_);
v___x_1160_ = lean_float_decLt(v___y_1156_, v___x_1159_);
v___y_1125_ = v___x_1160_;
goto v___jp_1124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_cls_1171_, lean_object* v_collapsed_1172_, lean_object* v_tag_1173_, lean_object* v_opts_1174_, lean_object* v_clsEnabled_1175_, lean_object* v_oldTraces_1176_, lean_object* v_msg_1177_, lean_object* v_resStartStop_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_collapsed_boxed_1184_; uint8_t v_clsEnabled_boxed_1185_; lean_object* v_res_1186_; 
v_collapsed_boxed_1184_ = lean_unbox(v_collapsed_1172_);
v_clsEnabled_boxed_1185_ = lean_unbox(v_clsEnabled_1175_);
v_res_1186_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1171_, v_collapsed_boxed_1184_, v_tag_1173_, v_opts_1174_, v_clsEnabled_boxed_1185_, v_oldTraces_1176_, v_msg_1177_, v_resStartStop_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec_ref(v_opts_1174_);
return v_res_1186_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1189_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = lean_box(0);
v___x_1193_ = lean_unsigned_to_nat(16u);
v___x_1194_ = lean_mk_array(v___x_1193_, v___x_1192_);
return v___x_1194_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___x_1195_);
return v___x_1197_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; lean_object* v___x_1201_; 
v___x_1198_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1199_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1200_ = 1;
v___x_1201_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1198_);
lean_ctor_set_uint8(v___x_1201_, sizeof(void*)*2, v___x_1200_);
return v___x_1201_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7(void){
_start:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1202_ = lean_unsigned_to_nat(32u);
v___x_1203_ = lean_mk_empty_array_with_capacity(v___x_1202_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
size_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1205_ = ((size_t)5ULL);
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_unsigned_to_nat(32u);
v___x_1208_ = lean_mk_empty_array_with_capacity(v___x_1207_);
v___x_1209_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7);
v___x_1210_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1208_);
lean_ctor_set(v___x_1210_, 2, v___x_1206_);
lean_ctor_set(v___x_1210_, 3, v___x_1206_);
lean_ctor_set_usize(v___x_1210_, 4, v___x_1205_);
return v___x_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1212_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
lean_ctor_set(v___x_1213_, 2, v___x_1212_);
lean_ctor_set(v___x_1213_, 3, v___x_1211_);
return v___x_1213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9);
v___x_1218_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v___x_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_declName_1220_, lean_object* v_as_1221_, size_t v_i_1222_, size_t v_stop_1223_, lean_object* v_b_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
uint8_t v___x_1230_; 
v___x_1230_ = lean_usize_dec_eq(v_i_1222_, v_stop_1223_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = lean_array_uget_borrowed(v_as_1221_, v_i_1222_);
lean_inc(v___x_1231_);
lean_inc(v_declName_1220_);
v___x_1232_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1220_, v___x_1231_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; size_t v___x_1234_; size_t v___x_1235_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v___x_1234_ = ((size_t)1ULL);
v___x_1235_ = lean_usize_add(v_i_1222_, v___x_1234_);
v_i_1222_ = v___x_1235_;
v_b_1224_ = v_a_1233_;
goto _start;
}
else
{
lean_dec(v_declName_1220_);
return v___x_1232_;
}
}
else
{
lean_object* v___x_1237_; 
lean_dec(v_declName_1220_);
v___x_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1237_, 0, v_b_1224_);
return v___x_1237_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1239_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1240_ = l_Lean_stringToMessageData(v___x_1239_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v_cls_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_cls_1253_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1254_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_1255_ = l_Lean_Name_append(v___x_1254_, v_cls_1253_);
return v___x_1255_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1256_; double v___x_1257_; 
v___x_1256_ = lean_unsigned_to_nat(1000000000u);
v___x_1257_ = lean_float_of_nat(v___x_1256_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1266_ = l_Lean_stringToMessageData(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1269_ = l_Lean_stringToMessageData(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1273_, lean_object* v___x_1274_, lean_object* v_declName_1275_, lean_object* v_____r_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1282_ = lean_array_get_size(v_val_1273_);
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_nat_dec_lt(v___x_1274_, v___x_1282_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_dec(v_declName_1275_);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
return v___x_1285_;
}
else
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_nat_dec_le(v___x_1282_, v___x_1282_);
if (v___x_1286_ == 0)
{
if (v___x_1284_ == 0)
{
lean_object* v___x_1287_; 
lean_dec(v_declName_1275_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1283_);
return v___x_1287_;
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1282_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1275_, v_val_1273_, v___x_1288_, v___x_1289_, v___x_1283_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1290_;
}
}
else
{
size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = lean_usize_of_nat(v___x_1282_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1275_, v_val_1273_, v___x_1291_, v___x_1292_, v___x_1283_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1293_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1302_ = l_Lean_stringToMessageData(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1305_ = l_Lean_stringToMessageData(v___x_1304_);
return v___x_1305_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1308_ = l_Lean_stringToMessageData(v___x_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1309_, lean_object* v_mvarId_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v_options_1322_; uint8_t v_hasTrace_1323_; 
v_options_1322_ = lean_ctor_get(v_a_1313_, 2);
v_hasTrace_1323_ = lean_ctor_get_uint8(v_options_1322_, sizeof(void*)*1);
if (v_hasTrace_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_inc(v_mvarId_1310_);
v___x_1324_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1497_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1497_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1497_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
uint8_t v___x_1329_; 
v___x_1329_ = lean_unbox(v_a_1325_);
lean_dec(v_a_1325_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_del_object(v___x_1327_);
lean_inc(v_mvarId_1310_);
v___x_1330_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1484_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1484_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1484_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_unbox(v_a_1331_);
lean_dec(v_a_1331_);
if (v___x_1335_ == 0)
{
lean_object* v___x_1336_; 
lean_del_object(v___x_1333_);
lean_inc(v_mvarId_1310_);
v___x_1336_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
if (lean_obj_tag(v_a_1337_) == 1)
{
lean_object* v_val_1338_; 
lean_dec(v_mvarId_1310_);
v_val_1338_ = lean_ctor_get(v_a_1337_, 0);
lean_inc(v_val_1338_);
lean_dec_ref_known(v_a_1337_, 1);
v_mvarId_1310_ = v_val_1338_;
goto _start;
}
else
{
lean_object* v___x_1340_; 
lean_dec(v_a_1337_);
lean_inc(v_mvarId_1310_);
v___x_1340_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
if (lean_obj_tag(v_a_1341_) == 1)
{
lean_object* v_val_1342_; 
lean_dec(v_mvarId_1310_);
v_val_1342_ = lean_ctor_get(v_a_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref_known(v_a_1341_, 1);
v_mvarId_1310_ = v_val_1342_;
goto _start;
}
else
{
uint8_t v___x_1344_; lean_object* v___x_1345_; 
lean_dec(v_a_1341_);
v___x_1344_ = 1;
lean_inc(v_mvarId_1310_);
v___x_1345_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1310_, v___x_1344_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
if (lean_obj_tag(v_a_1346_) == 1)
{
lean_object* v_val_1347_; 
lean_dec(v_mvarId_1310_);
v_val_1347_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_val_1347_);
lean_dec_ref_known(v_a_1346_, 1);
v_mvarId_1310_ = v_val_1347_;
goto _start;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_a_1346_);
v___x_1349_ = lean_unsigned_to_nat(100000u);
v___x_1350_ = lean_unsigned_to_nat(2u);
v___x_1351_ = 0;
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1353_, 0, v___x_1349_);
lean_ctor_set(v___x_1353_, 1, v___x_1350_);
lean_ctor_set(v___x_1353_, 2, v___x_1352_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 1, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 2, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 3, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 4, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 5, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 6, v___x_1351_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 7, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 8, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 9, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 10, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 11, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 12, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 13, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 14, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 15, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 16, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 17, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 18, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 19, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 20, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 21, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 22, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 23, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 24, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 25, v___x_1344_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 26, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 27, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1353_, sizeof(void*)*3 + 28, v_hasTrace_1323_);
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1356_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1357_ = l_Lean_Options_empty;
v___x_1358_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1353_, v___x_1355_, v___x_1356_, v___x_1357_, v_a_1311_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
lean_dec_ref_known(v___x_1358_, 1);
v___x_1360_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1310_);
v___x_1361_ = l_Lean_Meta_simpTargetStar(v_mvarId_1310_, v_a_1359_, v___x_1355_, v___x_1352_, v___x_1360_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1439_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1439_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1439_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_fst_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1437_; 
v_fst_1366_ = lean_ctor_get(v_a_1362_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1362_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_a_1362_, 1);
lean_dec(v_unused_1438_);
v___x_1368_ = v_a_1362_;
v_isShared_1369_ = v_isSharedCheck_1437_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_fst_1366_);
lean_dec(v_a_1362_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1437_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
switch(lean_obj_tag(v_fst_1366_))
{
case 0:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v___x_1370_ = lean_box(0);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1370_);
v___x_1372_ = v___x_1364_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
case 1:
{
lean_object* v___x_1374_; 
lean_del_object(v___x_1364_);
lean_inc(v_declName_1309_);
lean_inc(v_mvarId_1310_);
v___x_1374_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1310_, v_declName_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
if (lean_obj_tag(v_a_1375_) == 1)
{
lean_object* v_val_1376_; 
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1310_);
v_val_1376_ = lean_ctor_get(v_a_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v_a_1375_, 1);
v_mvarId_1310_ = v_val_1376_;
goto _start;
}
else
{
lean_object* v___x_1378_; 
lean_dec(v_a_1375_);
lean_inc(v_mvarId_1310_);
v___x_1378_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1418_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1418_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1418_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
if (lean_obj_tag(v_a_1379_) == 1)
{
lean_object* v_val_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1310_);
v_val_1383_ = lean_ctor_get(v_a_1379_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1379_, 1);
v___x_1384_ = lean_array_get_size(v_val_1383_);
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_nat_dec_lt(v___x_1354_, v___x_1384_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1388_; 
lean_dec(v_val_1383_);
lean_dec(v_declName_1309_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1385_);
v___x_1388_ = v___x_1381_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1385_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_nat_dec_le(v___x_1384_, v___x_1384_);
if (v___x_1390_ == 0)
{
if (v___x_1386_ == 0)
{
lean_object* v___x_1392_; 
lean_dec(v_val_1383_);
lean_dec(v_declName_1309_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1385_);
v___x_1392_ = v___x_1381_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1385_);
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
lean_del_object(v___x_1381_);
v___x_1394_ = ((size_t)0ULL);
v___x_1395_ = lean_usize_of_nat(v___x_1384_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1309_, v_val_1383_, v___x_1394_, v___x_1395_, v___x_1385_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_val_1383_);
return v___x_1396_;
}
}
else
{
size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
lean_del_object(v___x_1381_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = lean_usize_of_nat(v___x_1384_);
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1309_, v_val_1383_, v___x_1397_, v___x_1398_, v___x_1385_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_val_1383_);
return v___x_1399_;
}
}
}
else
{
lean_object* v___x_1400_; 
lean_del_object(v___x_1381_);
lean_dec(v_a_1379_);
lean_inc(v_mvarId_1310_);
v___x_1400_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1310_, v___x_1344_, v___x_1344_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v_a_1401_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___x_1400_, 1);
if (lean_obj_tag(v_a_1401_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1310_);
v_val_1402_ = lean_ctor_get(v_a_1401_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_a_1401_, 1);
v___x_1403_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1309_, v_val_1402_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1403_;
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_dec(v_a_1401_);
lean_dec(v_declName_1309_);
v___x_1404_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_mvarId_1310_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set_tag(v___x_1368_, 7);
lean_ctor_set(v___x_1368_, 1, v___x_1405_);
lean_ctor_set(v___x_1368_, 0, v___x_1404_);
v___x_1407_ = v___x_1368_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1404_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1407_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1408_;
}
}
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1410_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1400_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1400_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1419_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1378_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1378_);
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
else
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
lean_del_object(v___x_1368_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1427_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1374_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1374_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1435_; 
lean_del_object(v___x_1368_);
lean_del_object(v___x_1364_);
lean_dec(v_mvarId_1310_);
v_mvarId_1435_ = lean_ctor_get(v_fst_1366_, 0);
lean_inc(v_mvarId_1435_);
lean_dec_ref_known(v_fst_1366_, 1);
v_mvarId_1310_ = v_mvarId_1435_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1440_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1361_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1361_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1448_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1358_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1358_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1456_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1345_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1345_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1464_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1340_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1340_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1472_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1336_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1336_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v___x_1480_ = lean_box(0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1480_);
v___x_1482_ = v___x_1333_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
else
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1485_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v___x_1330_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1330_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
else
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v___x_1493_ = lean_box(0);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1493_);
v___x_1495_ = v___x_1327_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1498_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1324_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1324_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1506_; lean_object* v___f_1507_; lean_object* v_cls_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v_a_1515_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v_a_1527_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v_a_1532_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v_a_1543_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v_a_1558_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v_a_1563_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; 
v_inheritedTraceOptions_1506_ = lean_ctor_get(v_a_1313_, 13);
lean_inc(v_mvarId_1310_);
v___f_1507_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1507_, 0, v_mvarId_1310_);
v_cls_1508_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1509_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1510_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1511_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1506_, v_options_1322_, v___x_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1839_ = l_Lean_trace_profiler;
v___x_1840_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1322_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_dec_ref(v___f_1507_);
lean_inc(v_mvarId_1310_);
v___x_1841_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; uint8_t v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = lean_unbox(v_a_1842_);
lean_dec(v_a_1842_);
if (v___x_1843_ == 0)
{
lean_object* v___x_1844_; 
lean_inc(v_mvarId_1310_);
v___x_1844_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; uint8_t v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = lean_unbox(v_a_1845_);
lean_dec(v_a_1845_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
lean_inc(v_mvarId_1310_);
v___x_1847_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
if (lean_obj_tag(v_a_1848_) == 1)
{
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1849_; 
v_val_1849_ = lean_ctor_get(v_a_1848_, 0);
lean_inc(v_val_1849_);
lean_dec_ref_known(v_a_1848_, 1);
v_mvarId_1310_ = v_val_1849_;
goto _start;
}
else
{
lean_object* v_val_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_val_1851_ = lean_ctor_get(v_a_1848_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v_a_1848_, 1);
v___x_1852_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1853_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1852_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_dec_ref_known(v___x_1853_, 1);
v_mvarId_1310_ = v_val_1851_;
goto _start;
}
else
{
lean_dec(v_val_1851_);
lean_dec(v_declName_1309_);
return v___x_1853_;
}
}
}
else
{
lean_object* v___x_1855_; 
lean_dec(v_a_1848_);
lean_inc(v_mvarId_1310_);
v___x_1855_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
if (lean_obj_tag(v_a_1856_) == 1)
{
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1857_; 
v_val_1857_ = lean_ctor_get(v_a_1856_, 0);
lean_inc(v_val_1857_);
lean_dec_ref_known(v_a_1856_, 1);
v_mvarId_1310_ = v_val_1857_;
goto _start;
}
else
{
lean_object* v_val_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v_val_1859_ = lean_ctor_get(v_a_1856_, 0);
lean_inc(v_val_1859_);
lean_dec_ref_known(v_a_1856_, 1);
v___x_1860_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1861_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1860_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_dec_ref_known(v___x_1861_, 1);
v_mvarId_1310_ = v_val_1859_;
goto _start;
}
else
{
lean_dec(v_val_1859_);
lean_dec(v_declName_1309_);
return v___x_1861_;
}
}
}
else
{
lean_object* v___x_1863_; 
lean_dec(v_a_1856_);
lean_inc(v_mvarId_1310_);
v___x_1863_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1310_, v_hasTrace_1323_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
if (lean_obj_tag(v_a_1864_) == 1)
{
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1865_; 
v_val_1865_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_val_1865_);
lean_dec_ref_known(v_a_1864_, 1);
v_mvarId_1310_ = v_val_1865_;
goto _start;
}
else
{
lean_object* v_val_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_val_1867_ = lean_ctor_get(v_a_1864_, 0);
lean_inc(v_val_1867_);
lean_dec_ref_known(v_a_1864_, 1);
v___x_1868_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1869_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1868_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec_ref_known(v___x_1869_, 1);
v_mvarId_1310_ = v_val_1867_;
goto _start;
}
else
{
lean_dec(v_val_1867_);
lean_dec(v_declName_1309_);
return v___x_1869_;
}
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
lean_dec(v_a_1864_);
v___x_1871_ = lean_unsigned_to_nat(100000u);
v___x_1872_ = lean_unsigned_to_nat(2u);
v___x_1873_ = 0;
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1875_, 0, v___x_1871_);
lean_ctor_set(v___x_1875_, 1, v___x_1872_);
lean_ctor_set(v___x_1875_, 2, v___x_1874_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 1, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 2, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 3, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 4, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 5, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 6, v___x_1873_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 7, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 8, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 9, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 10, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 11, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 12, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 13, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 14, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 15, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 16, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 17, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 18, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 19, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 20, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 21, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 22, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 23, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 24, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 25, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 26, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 27, v___x_1840_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 28, v___x_1840_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1878_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1879_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1880_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
lean_ctor_set_uint8(v___x_1880_, sizeof(void*)*2, v_hasTrace_1323_);
v___x_1881_ = l_Lean_Options_empty;
v___x_1882_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1875_, v___x_1877_, v___x_1880_, v___x_1881_, v_a_1311_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1884_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1310_);
v___x_1885_ = l_Lean_Meta_simpTargetStar(v_mvarId_1310_, v_a_1883_, v___x_1877_, v___x_1874_, v___x_1884_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1984_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1984_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1984_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_fst_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1982_; 
v_fst_1890_ = lean_ctor_get(v_a_1886_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_a_1886_, 1);
lean_dec(v_unused_1983_);
v___x_1892_ = v_a_1886_;
v_isShared_1893_ = v_isSharedCheck_1982_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_fst_1890_);
lean_dec(v_a_1886_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1982_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
switch(lean_obj_tag(v_fst_1890_))
{
case 0:
{
lean_del_object(v___x_1892_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(0);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1894_);
v___x_1896_ = v___x_1888_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_del_object(v___x_1888_);
v___x_1898_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1899_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1898_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1899_;
}
}
case 1:
{
lean_object* v___x_1900_; 
lean_del_object(v___x_1888_);
lean_inc(v_declName_1309_);
lean_inc(v_mvarId_1310_);
v___x_1900_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1310_, v_declName_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
if (lean_obj_tag(v_a_1901_) == 1)
{
lean_del_object(v___x_1892_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1902_; 
v_val_1902_ = lean_ctor_get(v_a_1901_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v_a_1901_, 1);
v_mvarId_1310_ = v_val_1902_;
goto _start;
}
else
{
lean_object* v_val_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_val_1904_ = lean_ctor_get(v_a_1901_, 0);
lean_inc(v_val_1904_);
lean_dec_ref_known(v_a_1901_, 1);
v___x_1905_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1906_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1905_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_dec_ref_known(v___x_1906_, 1);
v_mvarId_1310_ = v_val_1904_;
goto _start;
}
else
{
lean_dec(v_val_1904_);
lean_dec(v_declName_1309_);
return v___x_1906_;
}
}
}
else
{
lean_object* v___x_1908_; 
lean_dec(v_a_1901_);
lean_inc(v_mvarId_1310_);
v___x_1908_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1959_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1911_ = v___x_1908_;
v_isShared_1912_ = v_isSharedCheck_1959_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1908_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1959_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
if (lean_obj_tag(v_a_1909_) == 1)
{
lean_object* v_val_1913_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; 
lean_del_object(v___x_1892_);
lean_dec(v_mvarId_1310_);
v_val_1913_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v_a_1909_, 1);
if (v___x_1511_ == 0)
{
v___y_1915_ = v_a_1311_;
v___y_1916_ = v_a_1312_;
v___y_1917_ = v_a_1313_;
v___y_1918_ = v_a_1314_;
goto v___jp_1914_;
}
else
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1936_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1935_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_dec_ref_known(v___x_1936_, 1);
v___y_1915_ = v_a_1311_;
v___y_1916_ = v_a_1312_;
v___y_1917_ = v_a_1313_;
v___y_1918_ = v_a_1314_;
goto v___jp_1914_;
}
else
{
lean_dec(v_val_1913_);
lean_del_object(v___x_1911_);
lean_dec(v_declName_1309_);
return v___x_1936_;
}
}
v___jp_1914_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1919_ = lean_array_get_size(v_val_1913_);
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_nat_dec_lt(v___x_1876_, v___x_1919_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1923_; 
lean_dec(v_val_1913_);
lean_dec(v_declName_1309_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1920_);
v___x_1923_ = v___x_1911_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1920_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_nat_dec_le(v___x_1919_, v___x_1919_);
if (v___x_1925_ == 0)
{
if (v___x_1921_ == 0)
{
lean_object* v___x_1927_; 
lean_dec(v_val_1913_);
lean_dec(v_declName_1309_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1920_);
v___x_1927_ = v___x_1911_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1920_);
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
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
lean_del_object(v___x_1911_);
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_of_nat(v___x_1919_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1309_, v_val_1913_, v___x_1929_, v___x_1930_, v___x_1920_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v_val_1913_);
return v___x_1931_;
}
}
else
{
size_t v___x_1932_; size_t v___x_1933_; lean_object* v___x_1934_; 
lean_del_object(v___x_1911_);
v___x_1932_ = ((size_t)0ULL);
v___x_1933_ = lean_usize_of_nat(v___x_1919_);
v___x_1934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1309_, v_val_1913_, v___x_1932_, v___x_1933_, v___x_1920_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v_val_1913_);
return v___x_1934_;
}
}
}
}
else
{
lean_object* v___x_1937_; 
lean_del_object(v___x_1911_);
lean_dec(v_a_1909_);
lean_inc(v_mvarId_1310_);
v___x_1937_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1310_, v_hasTrace_1323_, v_hasTrace_1323_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
if (lean_obj_tag(v_a_1938_) == 1)
{
lean_del_object(v___x_1892_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1939_; lean_object* v___x_1940_; 
v_val_1939_ = lean_ctor_get(v_a_1938_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v_a_1938_, 1);
v___x_1940_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1309_, v_val_1939_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1940_;
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_val_1941_ = lean_ctor_get(v_a_1938_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_a_1938_, 1);
v___x_1942_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1943_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1942_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref_known(v___x_1943_, 1);
v___x_1944_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1309_, v_val_1941_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1944_;
}
else
{
lean_dec(v_val_1941_);
lean_dec(v_declName_1309_);
return v___x_1943_;
}
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_dec(v_a_1938_);
lean_dec(v_declName_1309_);
v___x_1945_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_mvarId_1310_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 7);
lean_ctor_set(v___x_1892_, 1, v___x_1946_);
lean_ctor_set(v___x_1892_, 0, v___x_1945_);
v___x_1948_ = v___x_1892_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1945_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1948_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1949_;
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_del_object(v___x_1892_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1951_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1937_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1937_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_del_object(v___x_1892_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1960_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1908_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1908_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
lean_del_object(v___x_1892_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1968_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1900_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1900_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
default: 
{
lean_del_object(v___x_1892_);
lean_del_object(v___x_1888_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_mvarId_1976_; 
v_mvarId_1976_ = lean_ctor_get(v_fst_1890_, 0);
lean_inc(v_mvarId_1976_);
lean_dec_ref_known(v_fst_1890_, 1);
v_mvarId_1310_ = v_mvarId_1976_;
goto _start;
}
else
{
lean_object* v_mvarId_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_mvarId_1978_ = lean_ctor_get(v_fst_1890_, 0);
lean_inc(v_mvarId_1978_);
lean_dec_ref_known(v_fst_1890_, 1);
v___x_1979_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1980_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1979_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_dec_ref_known(v___x_1980_, 1);
v_mvarId_1310_ = v_mvarId_1978_;
goto _start;
}
else
{
lean_dec(v_mvarId_1978_);
lean_dec(v_declName_1309_);
return v___x_1980_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1985_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1885_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1885_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1993_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1882_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1882_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_2001_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1863_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1863_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_2009_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1855_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1855_);
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
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_2017_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1847_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1847_);
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
else
{
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
goto v___jp_1319_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2026_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_2025_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_dec_ref_known(v___x_2026_, 1);
goto v___jp_1319_;
}
else
{
return v___x_2026_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_2027_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1844_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1844_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
goto v___jp_1316_;
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2036_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_2035_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_dec_ref_known(v___x_2036_, 1);
goto v___jp_1316_;
}
else
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_2037_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1841_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1841_);
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
else
{
goto v___jp_1571_;
}
}
else
{
goto v___jp_1571_;
}
v___jp_1512_:
{
lean_object* v___x_1516_; double v___x_1517_; double v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1516_ = lean_io_get_num_heartbeats();
v___x_1517_ = lean_float_of_nat(v___y_1514_);
v___x_1518_ = lean_float_of_nat(v___x_1516_);
v___x_1519_ = lean_box_float(v___x_1517_);
v___x_1520_ = lean_box_float(v___x_1518_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_a_1515_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1508_, v_hasTrace_1323_, v___x_1509_, v_options_1322_, v___x_1511_, v___y_1513_, v___f_1507_, v___x_1522_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1523_;
}
v___jp_1524_:
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_a_1527_);
v___y_1513_ = v___y_1525_;
v___y_1514_ = v___y_1526_;
v_a_1515_ = v___x_1528_;
goto v___jp_1512_;
}
v___jp_1529_:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_a_1532_);
v___y_1513_ = v___y_1530_;
v___y_1514_ = v___y_1531_;
v_a_1515_ = v___x_1533_;
goto v___jp_1512_;
}
v___jp_1534_:
{
if (lean_obj_tag(v___y_1537_) == 0)
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___y_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___y_1537_, 1);
v___y_1530_ = v___y_1535_;
v___y_1531_ = v___y_1536_;
v_a_1532_ = v_a_1538_;
goto v___jp_1529_;
}
else
{
lean_object* v_a_1539_; 
v_a_1539_ = lean_ctor_get(v___y_1537_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___y_1537_, 1);
v___y_1525_ = v___y_1535_;
v___y_1526_ = v___y_1536_;
v_a_1527_ = v_a_1539_;
goto v___jp_1524_;
}
}
v___jp_1540_:
{
lean_object* v___x_1544_; double v___x_1545_; double v___x_1546_; double v___x_1547_; double v___x_1548_; double v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1544_ = lean_io_mono_nanos_now();
v___x_1545_ = lean_float_of_nat(v___y_1542_);
v___x_1546_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1547_ = lean_float_div(v___x_1545_, v___x_1546_);
v___x_1548_ = lean_float_of_nat(v___x_1544_);
v___x_1549_ = lean_float_div(v___x_1548_, v___x_1546_);
v___x_1550_ = lean_box_float(v___x_1547_);
v___x_1551_ = lean_box_float(v___x_1549_);
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v_a_1543_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1508_, v_hasTrace_1323_, v___x_1509_, v_options_1322_, v___x_1511_, v___y_1541_, v___f_1507_, v___x_1553_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1554_;
}
v___jp_1555_:
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v_a_1558_);
v___y_1541_ = v___y_1556_;
v___y_1542_ = v___y_1557_;
v_a_1543_ = v___x_1559_;
goto v___jp_1540_;
}
v___jp_1560_:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_a_1563_);
v___y_1541_ = v___y_1561_;
v___y_1542_ = v___y_1562_;
v_a_1543_ = v___x_1564_;
goto v___jp_1540_;
}
v___jp_1565_:
{
if (lean_obj_tag(v___y_1568_) == 0)
{
lean_object* v_a_1569_; 
v_a_1569_ = lean_ctor_get(v___y_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___y_1568_, 1);
v___y_1556_ = v___y_1566_;
v___y_1557_ = v___y_1567_;
v_a_1558_ = v_a_1569_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1570_; 
v_a_1570_ = lean_ctor_get(v___y_1568_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___y_1568_, 1);
v___y_1561_ = v___y_1566_;
v___y_1562_ = v___y_1567_;
v_a_1563_ = v_a_1570_;
goto v___jp_1560_;
}
}
v___jp_1571_:
{
lean_object* v___x_1572_; 
v___x_1572_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1314_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1575_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1322_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1310_);
v___x_1577_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; uint8_t v___x_1579_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v___x_1579_ = lean_unbox(v_a_1578_);
lean_dec(v_a_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; 
lean_inc(v_mvarId_1310_);
v___x_1580_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; uint8_t v___x_1582_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
v___x_1582_ = lean_unbox(v_a_1581_);
lean_dec(v_a_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
lean_inc(v_mvarId_1310_);
v___x_1583_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
if (lean_obj_tag(v_a_1584_) == 1)
{
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1585_; lean_object* v___x_1586_; 
v_val_1585_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_a_1584_, 1);
v___x_1586_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1585_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1586_;
goto v___jp_1565_;
}
else
{
lean_object* v_val_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_val_1587_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v_a_1584_, 1);
v___x_1588_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1589_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1588_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref_known(v___x_1589_, 1);
v___x_1590_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1587_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1590_;
goto v___jp_1565_;
}
else
{
lean_dec(v_val_1587_);
lean_dec(v_declName_1309_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1589_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v___x_1591_; 
lean_dec(v_a_1584_);
lean_inc(v_mvarId_1310_);
v___x_1591_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
if (lean_obj_tag(v_a_1592_) == 1)
{
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1593_; lean_object* v___x_1594_; 
v_val_1593_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v_a_1592_, 1);
v___x_1594_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1593_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1594_;
goto v___jp_1565_;
}
else
{
lean_object* v_val_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v_val_1595_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v_a_1592_, 1);
v___x_1596_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1597_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1596_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1598_; 
lean_dec_ref_known(v___x_1597_, 1);
v___x_1598_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1595_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1598_;
goto v___jp_1565_;
}
else
{
lean_dec(v_val_1595_);
lean_dec(v_declName_1309_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1597_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v___x_1599_; 
lean_dec(v_a_1592_);
lean_inc(v_mvarId_1310_);
v___x_1599_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1310_, v_hasTrace_1323_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v___x_1599_, 1);
if (lean_obj_tag(v_a_1600_) == 1)
{
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1601_; lean_object* v___x_1602_; 
v_val_1601_ = lean_ctor_get(v_a_1600_, 0);
lean_inc(v_val_1601_);
lean_dec_ref_known(v_a_1600_, 1);
v___x_1602_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1601_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1602_;
goto v___jp_1565_;
}
else
{
lean_object* v_val_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_val_1603_ = lean_ctor_get(v_a_1600_, 0);
lean_inc(v_val_1603_);
lean_dec_ref_known(v_a_1600_, 1);
v___x_1604_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1605_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1604_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref_known(v___x_1605_, 1);
v___x_1606_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1603_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1606_;
goto v___jp_1565_;
}
else
{
lean_dec(v_val_1603_);
lean_dec(v_declName_1309_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1605_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec(v_a_1600_);
v___x_1607_ = lean_unsigned_to_nat(100000u);
v___x_1608_ = lean_unsigned_to_nat(2u);
v___x_1609_ = 0;
v___x_1610_ = lean_box(0);
v___x_1611_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1611_, 0, v___x_1607_);
lean_ctor_set(v___x_1611_, 1, v___x_1608_);
lean_ctor_set(v___x_1611_, 2, v___x_1610_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 1, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 2, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 3, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 4, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 5, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 6, v___x_1609_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 7, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 8, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 9, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 10, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 11, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 12, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 13, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 14, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 15, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 16, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 17, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 18, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 19, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 20, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 21, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 22, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 23, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 24, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 25, v_hasTrace_1323_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 26, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 27, v___x_1575_);
lean_ctor_set_uint8(v___x_1611_, sizeof(void*)*3 + 28, v___x_1575_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1614_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1615_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1616_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
lean_ctor_set_uint8(v___x_1616_, sizeof(void*)*2, v_hasTrace_1323_);
v___x_1617_ = l_Lean_Options_empty;
v___x_1618_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1611_, v___x_1613_, v___x_1616_, v___x_1617_, v_a_1311_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1620_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1310_);
v___x_1621_ = l_Lean_Meta_simpTargetStar(v_mvarId_1310_, v_a_1619_, v___x_1613_, v___x_1610_, v___x_1620_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v_fst_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1677_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v___x_1621_, 1);
v_fst_1623_ = lean_ctor_get(v_a_1622_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_a_1622_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v_a_1622_, 1);
lean_dec(v_unused_1678_);
v___x_1625_ = v_a_1622_;
v_isShared_1626_ = v_isSharedCheck_1677_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_fst_1623_);
lean_dec(v_a_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1677_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
switch(lean_obj_tag(v_fst_1623_))
{
case 0:
{
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_box(0);
v___y_1556_ = v_a_1573_;
v___y_1557_ = v___x_1576_;
v_a_1558_ = v___x_1627_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1629_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1628_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1629_;
goto v___jp_1565_;
}
}
case 1:
{
lean_object* v___x_1630_; 
lean_inc(v_declName_1309_);
lean_inc(v_mvarId_1310_);
v___x_1630_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1310_, v_declName_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v___x_1630_, 1);
if (lean_obj_tag(v_a_1631_) == 1)
{
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1632_; lean_object* v___x_1633_; 
v_val_1632_ = lean_ctor_get(v_a_1631_, 0);
lean_inc(v_val_1632_);
lean_dec_ref_known(v_a_1631_, 1);
v___x_1633_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1632_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1633_;
goto v___jp_1565_;
}
else
{
lean_object* v_val_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_val_1634_ = lean_ctor_get(v_a_1631_, 0);
lean_inc(v_val_1634_);
lean_dec_ref_known(v_a_1631_, 1);
v___x_1635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1636_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1635_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref_known(v___x_1636_, 1);
v___x_1637_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1634_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1637_;
goto v___jp_1565_;
}
else
{
lean_dec(v_val_1634_);
lean_dec(v_declName_1309_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1636_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v___x_1638_; 
lean_dec(v_a_1631_);
lean_inc(v_mvarId_1310_);
v___x_1638_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
if (lean_obj_tag(v_a_1639_) == 1)
{
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v_val_1640_ = lean_ctor_get(v_a_1639_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_a_1639_, 1);
v___x_1641_ = lean_box(0);
v___x_1642_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1640_, v___x_1612_, v_declName_1309_, v___x_1641_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_val_1640_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1642_;
goto v___jp_1565_;
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_val_1643_ = lean_ctor_get(v_a_1639_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v_a_1639_, 1);
v___x_1644_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1645_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1644_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v___x_1647_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v___x_1647_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1643_, v___x_1612_, v_declName_1309_, v_a_1646_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_val_1643_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1647_;
goto v___jp_1565_;
}
else
{
lean_dec(v_val_1643_);
lean_dec(v_declName_1309_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1645_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v___x_1648_; 
lean_dec(v_a_1639_);
lean_inc(v_mvarId_1310_);
v___x_1648_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1310_, v_hasTrace_1323_, v_hasTrace_1323_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1667_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1667_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1667_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
if (lean_obj_tag(v_a_1649_) == 1)
{
lean_del_object(v___x_1651_);
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1653_; lean_object* v___x_1654_; 
v_val_1653_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_val_1653_);
lean_dec_ref_known(v_a_1649_, 1);
v___x_1654_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1309_, v_val_1653_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1654_;
goto v___jp_1565_;
}
else
{
lean_object* v_val_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_val_1655_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_val_1655_);
lean_dec_ref_known(v_a_1649_, 1);
v___x_1656_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1657_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1656_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref_known(v___x_1657_, 1);
v___x_1658_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1309_, v_val_1655_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1658_;
goto v___jp_1565_;
}
else
{
lean_dec(v_val_1655_);
lean_dec(v_declName_1309_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1657_;
goto v___jp_1565_;
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
lean_dec(v_a_1649_);
lean_dec(v_declName_1309_);
v___x_1659_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1652_ == 0)
{
lean_ctor_set_tag(v___x_1651_, 1);
lean_ctor_set(v___x_1651_, 0, v_mvarId_1310_);
v___x_1661_ = v___x_1651_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_mvarId_1310_);
v___x_1661_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
lean_object* v___x_1663_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 7);
lean_ctor_set(v___x_1625_, 1, v___x_1661_);
lean_ctor_set(v___x_1625_, 0, v___x_1659_);
v___x_1663_ = v___x_1625_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v___x_1661_);
v___x_1663_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1663_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1664_;
goto v___jp_1565_;
}
}
}
}
}
else
{
lean_object* v_a_1668_; 
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1668_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1668_);
lean_dec_ref_known(v___x_1648_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1668_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1669_; 
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1669_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v___x_1638_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1669_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1670_; 
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1670_ = lean_ctor_get(v___x_1630_, 0);
lean_inc(v_a_1670_);
lean_dec_ref_known(v___x_1630_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1670_;
goto v___jp_1560_;
}
}
default: 
{
lean_del_object(v___x_1625_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_mvarId_1671_; lean_object* v___x_1672_; 
v_mvarId_1671_ = lean_ctor_get(v_fst_1623_, 0);
lean_inc(v_mvarId_1671_);
lean_dec_ref_known(v_fst_1623_, 1);
v___x_1672_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_mvarId_1671_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1672_;
goto v___jp_1565_;
}
else
{
lean_object* v_mvarId_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_mvarId_1673_ = lean_ctor_get(v_fst_1623_, 0);
lean_inc(v_mvarId_1673_);
lean_dec_ref_known(v_fst_1623_, 1);
v___x_1674_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1675_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1674_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; 
lean_dec_ref_known(v___x_1675_, 1);
v___x_1676_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_mvarId_1673_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1676_;
goto v___jp_1565_;
}
else
{
lean_dec(v_mvarId_1673_);
lean_dec(v_declName_1309_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1675_;
goto v___jp_1565_;
}
}
}
}
}
}
else
{
lean_object* v_a_1679_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1679_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1621_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1679_;
goto v___jp_1560_;
}
}
else
{
lean_object* v_a_1680_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1680_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1618_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1680_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1681_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1681_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1599_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1681_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1682_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1682_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1591_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1682_;
goto v___jp_1560_;
}
}
}
else
{
lean_object* v_a_1683_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1683_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1583_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1683_;
goto v___jp_1560_;
}
}
else
{
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_box(0);
v___x_1685_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1684_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1685_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1687_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1686_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1688_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1689_;
goto v___jp_1565_;
}
else
{
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1687_;
goto v___jp_1565_;
}
}
}
}
else
{
lean_object* v_a_1690_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1690_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1580_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1690_;
goto v___jp_1560_;
}
}
else
{
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_box(0);
v___x_1692_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1691_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1692_;
goto v___jp_1565_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1694_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1693_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1696_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1695_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1696_;
goto v___jp_1565_;
}
else
{
v___y_1566_ = v_a_1573_;
v___y_1567_ = v___x_1576_;
v___y_1568_ = v___x_1694_;
goto v___jp_1565_;
}
}
}
}
else
{
lean_object* v_a_1697_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1697_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1577_, 1);
v___y_1561_ = v_a_1573_;
v___y_1562_ = v___x_1576_;
v_a_1563_ = v_a_1697_;
goto v___jp_1560_;
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1310_);
v___x_1699_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; uint8_t v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 1);
v___x_1701_ = lean_unbox(v_a_1700_);
lean_dec(v_a_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
lean_inc(v_mvarId_1310_);
v___x_1702_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; uint8_t v___x_1704_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref_known(v___x_1702_, 1);
v___x_1704_ = lean_unbox(v_a_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
lean_inc(v_mvarId_1310_);
v___x_1705_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v___x_1705_, 1);
if (lean_obj_tag(v_a_1706_) == 1)
{
lean_dec(v_a_1703_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1707_; lean_object* v___x_1708_; 
v_val_1707_ = lean_ctor_get(v_a_1706_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v_a_1706_, 1);
v___x_1708_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1707_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1708_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_val_1709_ = lean_ctor_get(v_a_1706_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1706_, 1);
v___x_1710_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1711_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1710_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v___x_1712_; 
lean_dec_ref_known(v___x_1711_, 1);
v___x_1712_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1709_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1712_;
goto v___jp_1534_;
}
else
{
lean_dec(v_val_1709_);
lean_dec(v_declName_1309_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1711_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1713_; 
lean_dec(v_a_1706_);
lean_inc(v_mvarId_1310_);
v___x_1713_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v___x_1713_, 1);
if (lean_obj_tag(v_a_1714_) == 1)
{
lean_dec(v_a_1703_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1715_; lean_object* v___x_1716_; 
v_val_1715_ = lean_ctor_get(v_a_1714_, 0);
lean_inc(v_val_1715_);
lean_dec_ref_known(v_a_1714_, 1);
v___x_1716_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1715_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1716_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_val_1717_ = lean_ctor_get(v_a_1714_, 0);
lean_inc(v_val_1717_);
lean_dec_ref_known(v_a_1714_, 1);
v___x_1718_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1719_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1718_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v___x_1720_; 
lean_dec_ref_known(v___x_1719_, 1);
v___x_1720_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1717_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1720_;
goto v___jp_1534_;
}
else
{
lean_dec(v_val_1717_);
lean_dec(v_declName_1309_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1719_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1721_; 
lean_dec(v_a_1714_);
lean_inc(v_mvarId_1310_);
v___x_1721_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1310_, v___x_1575_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
if (lean_obj_tag(v_a_1722_) == 1)
{
lean_dec(v_a_1703_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1723_; lean_object* v___x_1724_; 
v_val_1723_ = lean_ctor_get(v_a_1722_, 0);
lean_inc(v_val_1723_);
lean_dec_ref_known(v_a_1722_, 1);
v___x_1724_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1723_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1724_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_val_1725_ = lean_ctor_get(v_a_1722_, 0);
lean_inc(v_val_1725_);
lean_dec_ref_known(v_a_1722_, 1);
v___x_1726_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1727_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1726_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v___x_1728_; 
lean_dec_ref_known(v___x_1727_, 1);
v___x_1728_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1725_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1728_;
goto v___jp_1534_;
}
else
{
lean_dec(v_val_1725_);
lean_dec(v_declName_1309_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1727_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; uint8_t v___x_1734_; uint8_t v___x_1735_; uint8_t v___x_1736_; uint8_t v___x_1737_; uint8_t v___x_1738_; uint8_t v___x_1739_; uint8_t v___x_1740_; uint8_t v___x_1741_; uint8_t v___x_1742_; uint8_t v___x_1743_; uint8_t v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec(v_a_1722_);
v___x_1729_ = lean_unsigned_to_nat(100000u);
v___x_1730_ = lean_unsigned_to_nat(2u);
v___x_1731_ = 0;
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1733_, 0, v___x_1729_);
lean_ctor_set(v___x_1733_, 1, v___x_1730_);
lean_ctor_set(v___x_1733_, 2, v___x_1732_);
v___x_1734_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3, v___x_1734_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 1, v___x_1575_);
v___x_1735_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 2, v___x_1735_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 3, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 4, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 5, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 6, v___x_1731_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 7, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 8, v___x_1575_);
v___x_1736_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 9, v___x_1736_);
v___x_1737_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 10, v___x_1737_);
v___x_1738_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 11, v___x_1738_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 12, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 13, v___x_1575_);
v___x_1739_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 14, v___x_1739_);
v___x_1740_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 15, v___x_1740_);
v___x_1741_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 16, v___x_1741_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 17, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 18, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 19, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 20, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 21, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 22, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 23, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 24, v___x_1575_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 25, v___x_1575_);
v___x_1742_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 26, v___x_1742_);
v___x_1743_ = lean_unbox(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 27, v___x_1743_);
v___x_1744_ = lean_unbox(v_a_1703_);
lean_dec(v_a_1703_);
lean_ctor_set_uint8(v___x_1733_, sizeof(void*)*3 + 28, v___x_1744_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1747_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1748_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1749_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
lean_ctor_set_uint8(v___x_1749_, sizeof(void*)*2, v___x_1575_);
v___x_1750_ = l_Lean_Options_empty;
v___x_1751_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1733_, v___x_1746_, v___x_1749_, v___x_1750_, v_a_1311_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1310_);
v___x_1754_ = l_Lean_Meta_simpTargetStar(v_mvarId_1310_, v_a_1752_, v___x_1746_, v___x_1732_, v___x_1753_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_fst_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1810_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v_fst_1756_ = lean_ctor_get(v_a_1755_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_a_1755_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v_a_1755_, 1);
lean_dec(v_unused_1811_);
v___x_1758_ = v_a_1755_;
v_isShared_1759_ = v_isSharedCheck_1810_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_fst_1756_);
lean_dec(v_a_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1810_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
switch(lean_obj_tag(v_fst_1756_))
{
case 0:
{
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_box(0);
v___y_1530_ = v_a_1573_;
v___y_1531_ = v___x_1698_;
v_a_1532_ = v___x_1760_;
goto v___jp_1529_;
}
else
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1762_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1761_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1762_;
goto v___jp_1534_;
}
}
case 1:
{
lean_object* v___x_1763_; 
lean_inc(v_declName_1309_);
lean_inc(v_mvarId_1310_);
v___x_1763_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1310_, v_declName_1309_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
if (lean_obj_tag(v_a_1764_) == 1)
{
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1765_; lean_object* v___x_1766_; 
v_val_1765_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1765_);
lean_dec_ref_known(v_a_1764_, 1);
v___x_1766_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1765_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1766_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_val_1767_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v_a_1764_, 1);
v___x_1768_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1769_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1768_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v___x_1770_; 
lean_dec_ref_known(v___x_1769_, 1);
v___x_1770_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_val_1767_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1770_;
goto v___jp_1534_;
}
else
{
lean_dec(v_val_1767_);
lean_dec(v_declName_1309_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1769_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1771_; 
lean_dec(v_a_1764_);
lean_inc(v_mvarId_1310_);
v___x_1771_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
if (lean_obj_tag(v_a_1772_) == 1)
{
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_val_1773_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v_a_1772_, 1);
v___x_1774_ = lean_box(0);
v___x_1775_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1773_, v___x_1745_, v_declName_1309_, v___x_1774_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_val_1773_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1775_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v_val_1776_ = lean_ctor_get(v_a_1772_, 0);
lean_inc(v_val_1776_);
lean_dec_ref_known(v_a_1772_, 1);
v___x_1777_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1778_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1777_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
v___x_1780_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1776_, v___x_1745_, v_declName_1309_, v_a_1779_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
lean_dec(v_val_1776_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1780_;
goto v___jp_1534_;
}
else
{
lean_dec(v_val_1776_);
lean_dec(v_declName_1309_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1778_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1781_; 
lean_dec(v_a_1772_);
lean_inc(v_mvarId_1310_);
v___x_1781_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1310_, v___x_1575_, v___x_1575_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1800_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1784_ = v___x_1781_;
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1781_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1800_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
if (lean_obj_tag(v_a_1782_) == 1)
{
lean_del_object(v___x_1784_);
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_val_1786_; lean_object* v___x_1787_; 
v_val_1786_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_val_1786_);
lean_dec_ref_known(v_a_1782_, 1);
v___x_1787_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1309_, v_val_1786_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1787_;
goto v___jp_1534_;
}
else
{
lean_object* v_val_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_val_1788_ = lean_ctor_get(v_a_1782_, 0);
lean_inc(v_val_1788_);
lean_dec_ref_known(v_a_1782_, 1);
v___x_1789_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1790_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1789_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref_known(v___x_1790_, 1);
v___x_1791_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1309_, v_val_1788_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1791_;
goto v___jp_1534_;
}
else
{
lean_dec(v_val_1788_);
lean_dec(v_declName_1309_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1790_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_dec(v_a_1782_);
lean_dec(v_declName_1309_);
v___x_1792_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1785_ == 0)
{
lean_ctor_set_tag(v___x_1784_, 1);
lean_ctor_set(v___x_1784_, 0, v_mvarId_1310_);
v___x_1794_ = v___x_1784_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_mvarId_1310_);
v___x_1794_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set_tag(v___x_1758_, 7);
lean_ctor_set(v___x_1758_, 1, v___x_1794_);
lean_ctor_set(v___x_1758_, 0, v___x_1792_);
v___x_1796_ = v___x_1758_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1796_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1797_;
goto v___jp_1534_;
}
}
}
}
}
else
{
lean_object* v_a_1801_; 
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1801_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1781_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1801_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v_a_1802_; 
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1802_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1771_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1802_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v_a_1803_; 
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1803_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1763_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1803_;
goto v___jp_1524_;
}
}
default: 
{
lean_del_object(v___x_1758_);
lean_dec(v_mvarId_1310_);
if (v___x_1511_ == 0)
{
lean_object* v_mvarId_1804_; lean_object* v___x_1805_; 
v_mvarId_1804_ = lean_ctor_get(v_fst_1756_, 0);
lean_inc(v_mvarId_1804_);
lean_dec_ref_known(v_fst_1756_, 1);
v___x_1805_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_mvarId_1804_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1805_;
goto v___jp_1534_;
}
else
{
lean_object* v_mvarId_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_mvarId_1806_ = lean_ctor_get(v_fst_1756_, 0);
lean_inc(v_mvarId_1806_);
lean_dec_ref_known(v_fst_1756_, 1);
v___x_1807_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1808_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1807_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v___x_1809_; 
lean_dec_ref_known(v___x_1808_, 1);
v___x_1809_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1309_, v_mvarId_1806_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1809_;
goto v___jp_1534_;
}
else
{
lean_dec(v_mvarId_1806_);
lean_dec(v_declName_1309_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1808_;
goto v___jp_1534_;
}
}
}
}
}
}
else
{
lean_object* v_a_1812_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1812_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1754_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1812_;
goto v___jp_1524_;
}
}
else
{
lean_object* v_a_1813_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1813_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1813_);
lean_dec_ref_known(v___x_1751_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1813_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v_a_1814_; 
lean_dec(v_a_1703_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1814_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1814_);
lean_dec_ref_known(v___x_1721_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1814_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v_a_1815_; 
lean_dec(v_a_1703_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1815_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1713_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1815_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v_a_1816_; 
lean_dec(v_a_1703_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1816_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1705_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1816_;
goto v___jp_1524_;
}
}
else
{
lean_dec(v_a_1703_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = lean_box(0);
v___x_1818_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1817_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1818_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1820_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1819_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
v___x_1822_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1821_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1822_;
goto v___jp_1534_;
}
else
{
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1820_;
goto v___jp_1534_;
}
}
}
}
else
{
lean_object* v_a_1823_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1823_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1702_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1823_;
goto v___jp_1524_;
}
}
else
{
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = lean_box(0);
v___x_1825_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1824_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1825_;
goto v___jp_1534_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1827_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1508_, v___x_1826_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1828_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1829_;
goto v___jp_1534_;
}
else
{
v___y_1535_ = v_a_1573_;
v___y_1536_ = v___x_1698_;
v___y_1537_ = v___x_1827_;
goto v___jp_1534_;
}
}
}
}
else
{
lean_object* v_a_1830_; 
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1830_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1830_);
lean_dec_ref_known(v___x_1699_, 1);
v___y_1525_ = v_a_1573_;
v___y_1526_ = v___x_1698_;
v_a_1527_ = v_a_1830_;
goto v___jp_1524_;
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v___f_1507_);
lean_dec(v_mvarId_1310_);
lean_dec(v_declName_1309_);
v_a_1831_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1572_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1572_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
v___jp_1316_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
v___jp_1319_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2045_, lean_object* v_as_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
if (lean_obj_tag(v_as_2046_) == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec(v_declName_2045_);
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
else
{
lean_object* v_head_2054_; lean_object* v_tail_2055_; lean_object* v___x_2056_; 
v_head_2054_ = lean_ctor_get(v_as_2046_, 0);
lean_inc(v_head_2054_);
v_tail_2055_ = lean_ctor_get(v_as_2046_, 1);
lean_inc(v_tail_2055_);
lean_dec_ref_known(v_as_2046_, 2);
lean_inc(v_declName_2045_);
v___x_2056_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2045_, v_head_2054_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_dec_ref_known(v___x_2056_, 1);
v_as_2046_ = v_tail_2055_;
goto _start;
}
else
{
lean_dec(v_tail_2055_);
lean_dec(v_declName_2045_);
return v___x_2056_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2058_, lean_object* v_as_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2058_, v_as_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2066_, lean_object* v_as_2067_, lean_object* v_i_2068_, lean_object* v_stop_2069_, lean_object* v_b_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
size_t v_i_boxed_2076_; size_t v_stop_boxed_2077_; lean_object* v_res_2078_; 
v_i_boxed_2076_ = lean_unbox_usize(v_i_2068_);
lean_dec(v_i_2068_);
v_stop_boxed_2077_ = lean_unbox_usize(v_stop_2069_);
lean_dec(v_stop_2069_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2066_, v_as_2067_, v_i_boxed_2076_, v_stop_boxed_2077_, v_b_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_as_2067_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2079_, lean_object* v___x_2080_, lean_object* v_declName_2081_, lean_object* v_____r_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2079_, v___x_2080_, v_declName_2081_, v_____r_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___x_2080_);
lean_dec_ref(v_val_2079_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2089_, lean_object* v_mvarId_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2089_, v_mvarId_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_00_u03b1_2097_, lean_object* v_x_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_x_2098_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_00_u03b1_2105_, lean_object* v_x_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_00_u03b1_2105_, v_x_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2113_, uint8_t v_skipRealize_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v_env_2118_; uint8_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2117_ = lean_st_ref_get(v___y_2115_);
v_env_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc_ref(v_env_2118_);
lean_dec(v___x_2117_);
v___x_2119_ = l_Lean_Environment_contains(v_env_2118_, v_constName_2113_, v_skipRealize_2114_);
v___x_2120_ = lean_box(v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2122_, lean_object* v_skipRealize_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
uint8_t v_skipRealize_boxed_2126_; lean_object* v_res_2127_; 
v_skipRealize_boxed_2126_ = lean_unbox(v_skipRealize_2123_);
v_res_2127_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2122_, v_skipRealize_boxed_2126_, v___y_2124_);
lean_dec(v___y_2124_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2128_, uint8_t v_skipRealize_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2128_, v_skipRealize_2129_, v___y_2133_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2136_, lean_object* v_skipRealize_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v_skipRealize_boxed_2143_; lean_object* v_res_2144_; 
v_skipRealize_boxed_2143_ = lean_unbox(v_skipRealize_2137_);
v_res_2144_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2136_, v_skipRealize_boxed_2143_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2145_, lean_object* v___x_2146_, lean_object* v___x_2147_, lean_object* v_snd_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
lean_inc_ref(v_snd_2145_);
v___x_2154_ = l_Lean_Meta_mkCongrArg(v_snd_2145_, v___x_2146_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = l_Lean_Expr_app___override(v_snd_2145_, v___x_2147_);
v___x_2157_ = l_Lean_MVarId_replaceTargetEq(v_snd_2148_, v___x_2156_, v_a_2155_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2157_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec(v_snd_2148_);
lean_dec_ref(v___x_2147_);
lean_dec_ref(v_snd_2145_);
v_a_2158_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2154_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2154_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2166_, lean_object* v___x_2167_, lean_object* v___x_2168_, lean_object* v_snd_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2166_, v___x_2167_, v___x_2168_, v_snd_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2175_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2182_ = l_Lean_stringToMessageData(v___x_2181_);
return v___x_2182_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2184_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2185_ = l_Lean_stringToMessageData(v___x_2184_);
return v___x_2185_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2188_ = l_Lean_stringToMessageData(v___x_2187_);
return v___x_2188_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2191_ = l_Lean_stringToMessageData(v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2194_ = l_Lean_stringToMessageData(v___x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2198_, lean_object* v___x_2199_, lean_object* v_cls_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
lean_inc(v_mvarId_2198_);
v___x_2206_ = l_Lean_MVarId_getType(v_mvarId_2198_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2208_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
lean_inc(v_a_2207_);
lean_dec_ref_known(v___x_2206_, 1);
v___x_2208_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2207_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v_fst_2210_; lean_object* v_snd_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2364_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v_fst_2210_ = lean_ctor_get(v_a_2209_, 0);
v_snd_2211_ = lean_ctor_get(v_a_2209_, 1);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_a_2209_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2213_ = v_a_2209_;
v_isShared_2214_ = v_isSharedCheck_2364_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snd_2211_);
lean_inc(v_fst_2210_);
lean_dec(v_a_2209_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2364_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; lean_object* v___x_2220_; lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2363_; 
v___x_2215_ = l_Lean_Expr_getAppFn(v_fst_2210_);
v___x_2216_ = l_Lean_Expr_constName_x21(v___x_2215_);
v___x_2217_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2218_ = l_Lean_Name_str___override(v___x_2216_, v___x_2217_);
v___x_2219_ = 1;
lean_inc(v___x_2218_);
v___x_2220_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2218_, v___x_2219_, v___y_2204_);
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2363_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2363_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_nargs_2225_; lean_object* v___x_2226_; lean_object* v_dummy_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___y_2233_; lean_object* v___y_2234_; uint8_t v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; uint8_t v___x_2346_; 
v_nargs_2225_ = l_Lean_Expr_getAppNumArgs(v_fst_2210_);
v___x_2226_ = l_Lean_Expr_constLevels_x21(v___x_2215_);
lean_dec_ref(v___x_2215_);
v_dummy_2227_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
lean_inc(v_nargs_2225_);
v___x_2228_ = lean_mk_array(v_nargs_2225_, v_dummy_2227_);
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_sub(v_nargs_2225_, v___x_2229_);
lean_dec(v_nargs_2225_);
v___x_2231_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2210_, v___x_2228_, v___x_2230_);
v___x_2346_ = lean_unbox(v_a_2221_);
lean_dec(v_a_2221_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v___x_2231_);
lean_dec(v___x_2226_);
lean_del_object(v___x_2223_);
lean_del_object(v___x_2213_);
lean_dec(v_snd_2211_);
lean_dec(v_cls_2200_);
v___x_2347_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2348_ = l_Lean_MessageData_ofName(v___x_2218_);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2347_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_mvarId_2198_);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2351_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2353_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2354_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2354_);
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
else
{
v___y_2273_ = v___y_2201_;
v___y_2274_ = v___y_2202_;
v___y_2275_ = v___y_2203_;
v___y_2276_ = v___y_2204_;
goto v___jp_2272_;
}
v___jp_2232_:
{
lean_object* v___x_2241_; 
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
lean_inc(v___y_2238_);
lean_inc_ref(v___y_2237_);
lean_inc_ref(v___y_2234_);
v___x_2241_ = lean_infer_type(v___y_2234_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v___x_2243_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2244_ = l_Lean_MVarId_define(v_mvarId_2198_, v___x_2243_, v_a_2242_, v___y_2234_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2246_ = l_Lean_Meta_intro1Core(v_a_2245_, v___y_2235_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v_fst_2248_; lean_object* v_snd_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___f_2254_; lean_object* v___x_2255_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v_fst_2248_ = lean_ctor_get(v_a_2247_, 0);
lean_inc(v_fst_2248_);
v_snd_2249_ = lean_ctor_get(v_a_2247_, 1);
lean_inc_n(v_snd_2249_, 2);
lean_dec(v_a_2247_);
v___x_2250_ = l_Lean_Expr_appFn_x21(v___y_2233_);
lean_dec_ref(v___y_2233_);
v___x_2251_ = l_Lean_mkFVar(v_fst_2248_);
v___x_2252_ = l_Lean_Expr_app___override(v___x_2250_, v___x_2251_);
v___x_2253_ = l_Lean_mkAppN(v___y_2236_, v___x_2231_);
lean_dec_ref(v___x_2231_);
v___f_2254_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2254_, 0, v_snd_2211_);
lean_closure_set(v___f_2254_, 1, v___x_2253_);
lean_closure_set(v___f_2254_, 2, v___x_2252_);
lean_closure_set(v___f_2254_, 3, v_snd_2249_);
v___x_2255_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2249_, v___f_2254_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v___x_2255_;
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___x_2231_);
lean_dec(v_snd_2211_);
v_a_2256_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2246_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2246_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
else
{
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___x_2231_);
lean_dec(v_snd_2211_);
return v___x_2244_;
}
}
else
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec_ref(v___x_2231_);
lean_dec(v_snd_2211_);
lean_dec(v_mvarId_2198_);
v_a_2264_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2241_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2241_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_a_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
v___jp_2272_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_inc(v___x_2218_);
v___x_2277_ = l_Lean_mkConst(v___x_2218_, v___x_2226_);
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc_ref(v___x_2277_);
v___x_2278_ = lean_infer_type(v___x_2277_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref_known(v___x_2278_, 1);
v___x_2280_ = l_Lean_Meta_instantiateForall(v_a_2279_, v___x_2231_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___x_2282_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2283_ = lean_unsigned_to_nat(3u);
v___x_2284_ = l_Lean_Expr_isAppOfArity(v_a_2281_, v___x_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
lean_dec(v_a_2281_);
lean_dec_ref(v___x_2277_);
lean_dec_ref(v___x_2231_);
lean_dec(v_snd_2211_);
lean_dec(v_cls_2200_);
v___x_2285_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2286_ = l_Lean_MessageData_ofName(v___x_2218_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 7);
lean_ctor_set(v___x_2213_, 1, v___x_2286_);
lean_ctor_set(v___x_2213_, 0, v___x_2285_);
v___x_2288_ = v___x_2213_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2289_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set_tag(v___x_2223_, 1);
lean_ctor_set(v___x_2223_, 0, v_mvarId_2198_);
v___x_2292_ = v___x_2223_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_mvarId_2198_);
v___x_2292_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2290_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2293_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v___x_2294_;
}
}
}
else
{
lean_object* v_options_2297_; lean_object* v_inheritedTraceOptions_2298_; uint8_t v_hasTrace_2299_; lean_object* v___x_2300_; lean_object* v_nargs_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_del_object(v___x_2223_);
lean_dec(v___x_2218_);
v_options_2297_ = lean_ctor_get(v___y_2275_, 2);
v_inheritedTraceOptions_2298_ = lean_ctor_get(v___y_2275_, 13);
v_hasTrace_2299_ = lean_ctor_get_uint8(v_options_2297_, sizeof(void*)*1);
v___x_2300_ = l_Lean_Expr_appArg_x21(v_a_2281_);
lean_dec(v_a_2281_);
v_nargs_2301_ = l_Lean_Expr_getAppNumArgs(v___x_2300_);
lean_inc(v_nargs_2301_);
v___x_2302_ = lean_mk_array(v_nargs_2301_, v_dummy_2227_);
v___x_2303_ = lean_nat_sub(v_nargs_2301_, v___x_2229_);
lean_dec(v_nargs_2301_);
lean_inc_ref(v___x_2300_);
v___x_2304_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2300_, v___x_2302_, v___x_2303_);
v___x_2305_ = lean_array_get_size(v___x_2304_);
v___x_2306_ = lean_nat_sub(v___x_2305_, v___x_2229_);
v___x_2307_ = lean_array_get(v___x_2199_, v___x_2304_, v___x_2306_);
lean_dec(v___x_2306_);
lean_dec_ref(v___x_2304_);
if (v_hasTrace_2299_ == 0)
{
lean_del_object(v___x_2213_);
lean_dec(v_cls_2200_);
v___y_2233_ = v___x_2300_;
v___y_2234_ = v___x_2307_;
v___y_2235_ = v___x_2284_;
v___y_2236_ = v___x_2277_;
v___y_2237_ = v___y_2273_;
v___y_2238_ = v___y_2274_;
v___y_2239_ = v___y_2275_;
v___y_2240_ = v___y_2276_;
goto v___jp_2232_;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2200_);
v___x_2309_ = l_Lean_Name_append(v___x_2308_, v_cls_2200_);
v___x_2310_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2298_, v_options_2297_, v___x_2309_);
lean_dec(v___x_2309_);
if (v___x_2310_ == 0)
{
lean_del_object(v___x_2213_);
lean_dec(v_cls_2200_);
v___y_2233_ = v___x_2300_;
v___y_2234_ = v___x_2307_;
v___y_2235_ = v___x_2284_;
v___y_2236_ = v___x_2277_;
v___y_2237_ = v___y_2273_;
v___y_2238_ = v___y_2274_;
v___y_2239_ = v___y_2275_;
v___y_2240_ = v___y_2276_;
goto v___jp_2232_;
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2311_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2312_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2307_);
v___x_2313_ = l_Lean_inlineExpr(v___x_2307_, v___x_2312_);
if (v_isShared_2214_ == 0)
{
lean_ctor_set_tag(v___x_2213_, 7);
lean_ctor_set(v___x_2213_, 1, v___x_2313_);
lean_ctor_set(v___x_2213_, 0, v___x_2311_);
v___x_2315_ = v___x_2213_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2316_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
lean_inc_ref(v___x_2300_);
v___x_2318_ = l_Lean_indentExpr(v___x_2300_);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2200_, v___x_2319_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_dec_ref_known(v___x_2320_, 1);
v___y_2233_ = v___x_2300_;
v___y_2234_ = v___x_2307_;
v___y_2235_ = v___x_2284_;
v___y_2236_ = v___x_2277_;
v___y_2237_ = v___y_2273_;
v___y_2238_ = v___y_2274_;
v___y_2239_ = v___y_2275_;
v___y_2240_ = v___y_2276_;
goto v___jp_2232_;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v___x_2307_);
lean_dec_ref(v___x_2300_);
lean_dec_ref(v___x_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___x_2231_);
lean_dec(v_snd_2211_);
lean_dec(v_mvarId_2198_);
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
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
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec_ref(v___x_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___x_2231_);
lean_del_object(v___x_2223_);
lean_dec(v___x_2218_);
lean_del_object(v___x_2213_);
lean_dec(v_snd_2211_);
lean_dec(v_cls_2200_);
lean_dec(v_mvarId_2198_);
v_a_2330_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2280_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2280_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec_ref(v___x_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v___x_2231_);
lean_del_object(v___x_2223_);
lean_dec(v___x_2218_);
lean_del_object(v___x_2213_);
lean_dec(v_snd_2211_);
lean_dec(v_cls_2200_);
lean_dec(v_mvarId_2198_);
v_a_2338_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2278_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2278_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_cls_2200_);
lean_dec(v_mvarId_2198_);
v_a_2365_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2208_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2208_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v_cls_2200_);
lean_dec(v_mvarId_2198_);
v_a_2373_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2206_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2206_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2381_, lean_object* v___x_2382_, lean_object* v_cls_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2381_, v___x_2382_, v_cls_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec_ref(v___x_2382_);
return v_res_2389_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2393_, lean_object* v_x_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2400_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v_mvarId_2393_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2404_, v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_x_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2412_, lean_object* v_mvarId_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_options_2419_; lean_object* v_inheritedTraceOptions_2420_; uint8_t v_hasTrace_2421_; lean_object* v___x_2422_; lean_object* v_cls_2423_; lean_object* v___f_2424_; 
v_options_2419_ = lean_ctor_get(v_a_2416_, 2);
v_inheritedTraceOptions_2420_ = lean_ctor_get(v_a_2416_, 13);
v_hasTrace_2421_ = lean_ctor_get_uint8(v_options_2419_, sizeof(void*)*1);
v___x_2422_ = l_Lean_instInhabitedExpr;
v_cls_2423_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2413_);
v___f_2424_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2424_, 0, v_mvarId_2413_);
lean_closure_set(v___f_2424_, 1, v___x_2422_);
lean_closure_set(v___f_2424_, 2, v_cls_2423_);
if (v_hasTrace_2421_ == 0)
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2413_, v___f_2424_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2412_, v_a_2426_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2427_;
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_declName_2412_);
v_a_2428_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2425_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2425_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
else
{
lean_object* v___f_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; uint8_t v___x_2439_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v_a_2443_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v_a_2458_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v_a_2463_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v_a_2475_; 
lean_inc(v_mvarId_2413_);
v___f_2436_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2436_, 0, v_mvarId_2413_);
v___x_2437_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2438_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2439_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2420_, v_options_2419_, v___x_2438_);
if (v___x_2439_ == 0)
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = l_Lean_trace_profiler;
v___x_2511_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2419_, v___x_2510_);
if (v___x_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_dec_ref(v___f_2436_);
v___x_2512_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2413_, v___f_2424_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2412_, v_a_2513_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2514_;
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_declName_2412_);
v_a_2515_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2512_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2512_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
goto v___jp_2477_;
}
}
else
{
goto v___jp_2477_;
}
v___jp_2440_:
{
lean_object* v___x_2444_; double v___x_2445_; double v___x_2446_; double v___x_2447_; double v___x_2448_; double v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2444_ = lean_io_mono_nanos_now();
v___x_2445_ = lean_float_of_nat(v___y_2442_);
v___x_2446_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2447_ = lean_float_div(v___x_2445_, v___x_2446_);
v___x_2448_ = lean_float_of_nat(v___x_2444_);
v___x_2449_ = lean_float_div(v___x_2448_, v___x_2446_);
v___x_2450_ = lean_box_float(v___x_2447_);
v___x_2451_ = lean_box_float(v___x_2449_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2450_);
lean_ctor_set(v___x_2452_, 1, v___x_2451_);
v___x_2453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2453_, 0, v_a_2443_);
lean_ctor_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2423_, v_hasTrace_2421_, v___x_2437_, v_options_2419_, v___x_2439_, v___y_2441_, v___f_2436_, v___x_2453_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2454_;
}
v___jp_2455_:
{
lean_object* v___x_2459_; 
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v_a_2458_);
v___y_2441_ = v___y_2456_;
v___y_2442_ = v___y_2457_;
v_a_2443_ = v___x_2459_;
goto v___jp_2440_;
}
v___jp_2460_:
{
lean_object* v___x_2464_; double v___x_2465_; double v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2464_ = lean_io_get_num_heartbeats();
v___x_2465_ = lean_float_of_nat(v___y_2462_);
v___x_2466_ = lean_float_of_nat(v___x_2464_);
v___x_2467_ = lean_box_float(v___x_2465_);
v___x_2468_ = lean_box_float(v___x_2466_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2467_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2463_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2423_, v_hasTrace_2421_, v___x_2437_, v_options_2419_, v___x_2439_, v___y_2461_, v___f_2436_, v___x_2470_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
return v___x_2471_;
}
v___jp_2472_:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2476_, 0, v_a_2475_);
v___y_2461_ = v___y_2474_;
v___y_2462_ = v___y_2473_;
v_a_2463_ = v___x_2476_;
goto v___jp_2460_;
}
v___jp_2477_:
{
lean_object* v___x_2478_; lean_object* v_a_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; 
v___x_2478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2417_);
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_a_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2481_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2419_, v___x_2480_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_io_mono_nanos_now();
v___x_2483_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2413_, v___f_2424_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2485_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v___x_2485_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2412_, v_a_2484_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2485_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2485_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 1);
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
v___y_2441_ = v_a_2479_;
v___y_2442_ = v___x_2482_;
v_a_2443_ = v___x_2491_;
goto v___jp_2440_;
}
}
}
else
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2485_, 1);
v___y_2456_ = v_a_2479_;
v___y_2457_ = v___x_2482_;
v_a_2458_ = v_a_2494_;
goto v___jp_2455_;
}
}
else
{
lean_object* v_a_2495_; 
lean_dec(v_declName_2412_);
v_a_2495_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2483_, 1);
v___y_2456_ = v_a_2479_;
v___y_2457_ = v___x_2482_;
v_a_2458_ = v_a_2495_;
goto v___jp_2455_;
}
}
else
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_io_get_num_heartbeats();
v___x_2497_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2413_, v___f_2424_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2499_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2499_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2412_, v_a_2498_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2499_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2499_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 1);
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
v___y_2461_ = v_a_2479_;
v___y_2462_ = v___x_2496_;
v_a_2463_ = v___x_2505_;
goto v___jp_2460_;
}
}
}
else
{
lean_object* v_a_2508_; 
v_a_2508_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2499_, 1);
v___y_2473_ = v___x_2496_;
v___y_2474_ = v_a_2479_;
v_a_2475_ = v_a_2508_;
goto v___jp_2472_;
}
}
else
{
lean_object* v_a_2509_; 
lean_dec(v_declName_2412_);
v_a_2509_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2497_, 1);
v___y_2473_ = v___x_2496_;
v___y_2474_ = v_a_2479_;
v_a_2475_ = v_a_2509_;
goto v___jp_2472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2523_, lean_object* v_mvarId_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2523_, v_mvarId_2524_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_);
lean_dec(v_a_2528_);
lean_dec_ref(v_a_2527_);
lean_dec(v_a_2526_);
lean_dec_ref(v_a_2525_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v___x_2534_; 
v___x_2534_ = l_Lean_Expr_hasMVar(v_e_2531_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_e_2531_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; lean_object* v_mctx_2537_; lean_object* v___x_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; lean_object* v___x_2541_; lean_object* v_cache_2542_; lean_object* v_zetaDeltaFVarIds_2543_; lean_object* v_postponed_2544_; lean_object* v_diag_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2554_; 
v___x_2536_ = lean_st_ref_get(v___y_2532_);
v_mctx_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_mctx_2537_);
lean_dec(v___x_2536_);
v___x_2538_ = l_Lean_instantiateMVarsCore(v_mctx_2537_, v_e_2531_);
v_fst_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_fst_2539_);
v_snd_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_snd_2540_);
lean_dec_ref(v___x_2538_);
v___x_2541_ = lean_st_ref_take(v___y_2532_);
v_cache_2542_ = lean_ctor_get(v___x_2541_, 1);
v_zetaDeltaFVarIds_2543_ = lean_ctor_get(v___x_2541_, 2);
v_postponed_2544_ = lean_ctor_get(v___x_2541_, 3);
v_diag_2545_ = lean_ctor_get(v___x_2541_, 4);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2541_, 0);
lean_dec(v_unused_2555_);
v___x_2547_ = v___x_2541_;
v_isShared_2548_ = v_isSharedCheck_2554_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_diag_2545_);
lean_inc(v_postponed_2544_);
lean_inc(v_zetaDeltaFVarIds_2543_);
lean_inc(v_cache_2542_);
lean_dec(v___x_2541_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2554_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_snd_2540_);
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_snd_2540_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_cache_2542_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_zetaDeltaFVarIds_2543_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_postponed_2544_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_diag_2545_);
v___x_2550_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_st_ref_set(v___y_2532_, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_fst_2539_);
return v___x_2552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2556_, v___y_2557_);
lean_dec(v___y_2557_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2560_, v___y_2562_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2574_, uint8_t v_allowLevelAssignments_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2575_, v_k_2574_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
v_a_2590_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2581_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2581_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2598_, lean_object* v_allowLevelAssignments_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2605_; lean_object* v_res_2606_; 
v_allowLevelAssignments_boxed_2605_ = lean_unbox(v_allowLevelAssignments_2599_);
v_res_2606_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2598_, v_allowLevelAssignments_boxed_2605_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2607_, lean_object* v_k_2608_, uint8_t v_allowLevelAssignments_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2608_, v_allowLevelAssignments_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2616_, lean_object* v_k_2617_, lean_object* v_allowLevelAssignments_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2624_; lean_object* v_res_2625_; 
v_allowLevelAssignments_boxed_2624_ = lean_unbox(v_allowLevelAssignments_2618_);
v_res_2625_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2616_, v_k_2617_, v_allowLevelAssignments_boxed_2624_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2626_, lean_object* v_e_2627_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = l_Lean_indentD(v_e_2627_);
v___x_2629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2626_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2630_, lean_object* v___x_2631_, lean_object* v_declName_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2630_, v___x_2631_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = l_Lean_Expr_mvarId_x21(v_a_2639_);
v___x_2641_ = l_Lean_MVarId_intros(v___x_2640_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v_snd_2643_; lean_object* v___x_2644_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v_snd_2643_ = lean_ctor_get(v_a_2642_, 1);
lean_inc_n(v_snd_2643_, 2);
lean_dec(v_a_2642_);
v___x_2644_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2643_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; uint8_t v___x_2646_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = lean_unbox(v_a_2645_);
lean_dec(v_a_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2643_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2649_; 
v_a_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_a_2648_);
lean_dec_ref_known(v___x_2647_, 1);
v___x_2649_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2632_, v_a_2648_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref_known(v___x_2649_, 1);
v___x_2650_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2639_, v___y_2634_);
return v___x_2650_;
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
lean_dec(v_a_2639_);
v_a_2651_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2649_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2649_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
lean_dec(v_a_2639_);
lean_dec(v_declName_2632_);
v_a_2659_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2666_ == 0)
{
v___x_2661_ = v___x_2647_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2647_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2659_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
else
{
lean_object* v___x_2667_; 
lean_dec(v_snd_2643_);
lean_dec(v_declName_2632_);
v___x_2667_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2639_, v___y_2634_);
return v___x_2667_;
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_snd_2643_);
lean_dec(v_a_2639_);
lean_dec(v_declName_2632_);
v_a_2668_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2644_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2644_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_a_2639_);
lean_dec(v_declName_2632_);
v_a_2676_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2641_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2641_);
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
else
{
lean_dec(v_declName_2632_);
return v___x_2638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2684_, lean_object* v___x_2685_, lean_object* v_declName_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2684_, v___x_2685_, v_declName_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
return v_res_2692_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2695_ = l_Lean_stringToMessageData(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2703_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2704_ = l_Lean_indentExpr(v_type_2696_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2707_, lean_object* v_x_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2707_, v_x_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_x_2708_);
return v_res_2714_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2715_){
_start:
{
if (lean_obj_tag(v_e_2715_) == 0)
{
uint8_t v___x_2716_; 
v___x_2716_ = 2;
return v___x_2716_;
}
else
{
lean_object* v_a_2717_; uint8_t v___x_2718_; 
v_a_2717_ = lean_ctor_get(v_e_2715_, 0);
v___x_2718_ = l_Lean_Expr_hasSyntheticSorry(v_a_2717_);
if (v___x_2718_ == 0)
{
uint8_t v___x_2719_; 
v___x_2719_ = 0;
return v___x_2719_;
}
else
{
uint8_t v___x_2720_; 
v___x_2720_ = 1;
return v___x_2720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2721_){
_start:
{
uint8_t v_res_2722_; lean_object* v_r_2723_; 
v_res_2722_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2721_);
lean_dec_ref(v_e_2721_);
v_r_2723_ = lean_box(v_res_2722_);
return v_r_2723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2724_, uint8_t v_collapsed_2725_, lean_object* v_tag_2726_, lean_object* v_opts_2727_, uint8_t v_clsEnabled_2728_, lean_object* v_oldTraces_2729_, lean_object* v_msg_2730_, lean_object* v_resStartStop_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_fst_2737_; lean_object* v_snd_2738_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v_data_2742_; lean_object* v_fst_2753_; lean_object* v_snd_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; lean_object* v___y_2758_; lean_object* v_a_2759_; uint8_t v___y_2774_; double v___y_2805_; 
v_fst_2737_ = lean_ctor_get(v_resStartStop_2731_, 0);
lean_inc(v_fst_2737_);
v_snd_2738_ = lean_ctor_get(v_resStartStop_2731_, 1);
lean_inc(v_snd_2738_);
lean_dec_ref(v_resStartStop_2731_);
v_fst_2753_ = lean_ctor_get(v_snd_2738_, 0);
lean_inc(v_fst_2753_);
v_snd_2754_ = lean_ctor_get(v_snd_2738_, 1);
lean_inc(v_snd_2754_);
lean_dec(v_snd_2738_);
v___x_2755_ = l_Lean_trace_profiler;
v___x_2756_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2727_, v___x_2755_);
if (v___x_2756_ == 0)
{
v___y_2774_ = v___x_2756_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2810_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2811_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2727_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; double v___x_2814_; double v___x_2815_; double v___x_2816_; 
v___x_2812_ = l_Lean_trace_profiler_threshold;
v___x_2813_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2727_, v___x_2812_);
v___x_2814_ = lean_float_of_nat(v___x_2813_);
v___x_2815_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2);
v___x_2816_ = lean_float_div(v___x_2814_, v___x_2815_);
v___y_2805_ = v___x_2816_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2817_; lean_object* v___x_2818_; double v___x_2819_; 
v___x_2817_ = l_Lean_trace_profiler_threshold;
v___x_2818_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2727_, v___x_2817_);
v___x_2819_ = lean_float_of_nat(v___x_2818_);
v___y_2805_ = v___x_2819_;
goto v___jp_2804_;
}
}
v___jp_2739_:
{
lean_object* v___x_2743_; 
lean_inc(v___y_2741_);
v___x_2743_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_oldTraces_2729_, v_data_2742_, v___y_2741_, v___y_2740_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v___x_2744_; 
lean_dec_ref_known(v___x_2743_, 1);
v___x_2744_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2737_);
return v___x_2744_;
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_fst_2737_);
v_a_2745_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2743_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2743_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
v___jp_2757_:
{
uint8_t v_result_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; double v___x_2763_; lean_object* v_data_2764_; 
v_result_2760_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2737_);
v___x_2761_ = lean_box(v_result_2760_);
v___x_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
v___x_2763_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2726_);
lean_inc_ref(v___x_2762_);
lean_inc(v_cls_2724_);
v_data_2764_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2764_, 0, v_cls_2724_);
lean_ctor_set(v_data_2764_, 1, v___x_2762_);
lean_ctor_set(v_data_2764_, 2, v_tag_2726_);
lean_ctor_set_float(v_data_2764_, sizeof(void*)*3, v___x_2763_);
lean_ctor_set_float(v_data_2764_, sizeof(void*)*3 + 8, v___x_2763_);
lean_ctor_set_uint8(v_data_2764_, sizeof(void*)*3 + 16, v_collapsed_2725_);
if (v___x_2756_ == 0)
{
lean_dec_ref_known(v___x_2762_, 1);
lean_dec(v_snd_2754_);
lean_dec(v_fst_2753_);
lean_dec_ref(v_tag_2726_);
lean_dec(v_cls_2724_);
v___y_2740_ = v_a_2759_;
v___y_2741_ = v___y_2758_;
v_data_2742_ = v_data_2764_;
goto v___jp_2739_;
}
else
{
lean_object* v_data_2765_; double v___x_2766_; double v___x_2767_; 
lean_dec_ref_known(v_data_2764_, 3);
v_data_2765_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2765_, 0, v_cls_2724_);
lean_ctor_set(v_data_2765_, 1, v___x_2762_);
lean_ctor_set(v_data_2765_, 2, v_tag_2726_);
v___x_2766_ = lean_unbox_float(v_fst_2753_);
lean_dec(v_fst_2753_);
lean_ctor_set_float(v_data_2765_, sizeof(void*)*3, v___x_2766_);
v___x_2767_ = lean_unbox_float(v_snd_2754_);
lean_dec(v_snd_2754_);
lean_ctor_set_float(v_data_2765_, sizeof(void*)*3 + 8, v___x_2767_);
lean_ctor_set_uint8(v_data_2765_, sizeof(void*)*3 + 16, v_collapsed_2725_);
v___y_2740_ = v_a_2759_;
v___y_2741_ = v___y_2758_;
v_data_2742_ = v_data_2765_;
goto v___jp_2739_;
}
}
v___jp_2768_:
{
lean_object* v_ref_2769_; lean_object* v___x_2770_; 
v_ref_2769_ = lean_ctor_get(v___y_2734_, 5);
lean_inc(v___y_2735_);
lean_inc_ref(v___y_2734_);
lean_inc(v___y_2733_);
lean_inc_ref(v___y_2732_);
lean_inc(v_fst_2737_);
v___x_2770_ = lean_apply_6(v_msg_2730_, v_fst_2737_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, lean_box(0));
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v___y_2758_ = v_ref_2769_;
v_a_2759_ = v_a_2771_;
goto v___jp_2757_;
}
else
{
lean_object* v___x_2772_; 
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
v___y_2758_ = v_ref_2769_;
v_a_2759_ = v___x_2772_;
goto v___jp_2757_;
}
}
v___jp_2773_:
{
if (v_clsEnabled_2728_ == 0)
{
if (v___y_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v_traceState_2776_; lean_object* v_env_2777_; lean_object* v_nextMacroScope_2778_; lean_object* v_ngen_2779_; lean_object* v_auxDeclNGen_2780_; lean_object* v_cache_2781_; lean_object* v_messages_2782_; lean_object* v_infoState_2783_; lean_object* v_snapshotTasks_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_snd_2754_);
lean_dec(v_fst_2753_);
lean_dec_ref(v_msg_2730_);
lean_dec_ref(v_tag_2726_);
lean_dec(v_cls_2724_);
v___x_2775_ = lean_st_ref_take(v___y_2735_);
v_traceState_2776_ = lean_ctor_get(v___x_2775_, 4);
v_env_2777_ = lean_ctor_get(v___x_2775_, 0);
v_nextMacroScope_2778_ = lean_ctor_get(v___x_2775_, 1);
v_ngen_2779_ = lean_ctor_get(v___x_2775_, 2);
v_auxDeclNGen_2780_ = lean_ctor_get(v___x_2775_, 3);
v_cache_2781_ = lean_ctor_get(v___x_2775_, 5);
v_messages_2782_ = lean_ctor_get(v___x_2775_, 6);
v_infoState_2783_ = lean_ctor_get(v___x_2775_, 7);
v_snapshotTasks_2784_ = lean_ctor_get(v___x_2775_, 8);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2786_ = v___x_2775_;
v_isShared_2787_ = v_isSharedCheck_2803_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_snapshotTasks_2784_);
lean_inc(v_infoState_2783_);
lean_inc(v_messages_2782_);
lean_inc(v_cache_2781_);
lean_inc(v_traceState_2776_);
lean_inc(v_auxDeclNGen_2780_);
lean_inc(v_ngen_2779_);
lean_inc(v_nextMacroScope_2778_);
lean_inc(v_env_2777_);
lean_dec(v___x_2775_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2803_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
uint64_t v_tid_2788_; lean_object* v_traces_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2802_; 
v_tid_2788_ = lean_ctor_get_uint64(v_traceState_2776_, sizeof(void*)*1);
v_traces_2789_ = lean_ctor_get(v_traceState_2776_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_traceState_2776_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2791_ = v_traceState_2776_;
v_isShared_2792_ = v_isSharedCheck_2802_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_traces_2789_);
lean_dec(v_traceState_2776_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2802_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2729_, v_traces_2789_);
lean_dec_ref(v_traces_2789_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2793_);
v___x_2795_ = v___x_2791_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2793_);
lean_ctor_set_uint64(v_reuseFailAlloc_2801_, sizeof(void*)*1, v_tid_2788_);
v___x_2795_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2797_; 
if (v_isShared_2787_ == 0)
{
lean_ctor_set(v___x_2786_, 4, v___x_2795_);
v___x_2797_ = v___x_2786_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_env_2777_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_nextMacroScope_2778_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_ngen_2779_);
lean_ctor_set(v_reuseFailAlloc_2800_, 3, v_auxDeclNGen_2780_);
lean_ctor_set(v_reuseFailAlloc_2800_, 4, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2800_, 5, v_cache_2781_);
lean_ctor_set(v_reuseFailAlloc_2800_, 6, v_messages_2782_);
lean_ctor_set(v_reuseFailAlloc_2800_, 7, v_infoState_2783_);
lean_ctor_set(v_reuseFailAlloc_2800_, 8, v_snapshotTasks_2784_);
v___x_2797_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_st_ref_set(v___y_2735_, v___x_2797_);
v___x_2799_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___redArg(v_fst_2737_);
return v___x_2799_;
}
}
}
}
}
else
{
goto v___jp_2768_;
}
}
else
{
goto v___jp_2768_;
}
}
v___jp_2804_:
{
double v___x_2806_; double v___x_2807_; double v___x_2808_; uint8_t v___x_2809_; 
v___x_2806_ = lean_unbox_float(v_snd_2754_);
v___x_2807_ = lean_unbox_float(v_fst_2753_);
v___x_2808_ = lean_float_sub(v___x_2806_, v___x_2807_);
v___x_2809_ = lean_float_decLt(v___y_2805_, v___x_2808_);
v___y_2774_ = v___x_2809_;
goto v___jp_2773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2820_, lean_object* v_collapsed_2821_, lean_object* v_tag_2822_, lean_object* v_opts_2823_, lean_object* v_clsEnabled_2824_, lean_object* v_oldTraces_2825_, lean_object* v_msg_2826_, lean_object* v_resStartStop_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
uint8_t v_collapsed_boxed_2833_; uint8_t v_clsEnabled_boxed_2834_; lean_object* v_res_2835_; 
v_collapsed_boxed_2833_ = lean_unbox(v_collapsed_2821_);
v_clsEnabled_boxed_2834_ = lean_unbox(v_clsEnabled_2824_);
v_res_2835_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2820_, v_collapsed_boxed_2833_, v_tag_2822_, v_opts_2823_, v_clsEnabled_boxed_2834_, v_oldTraces_2825_, v_msg_2826_, v_resStartStop_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v_opts_2823_);
return v_res_2835_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2838_ = l_Lean_stringToMessageData(v___x_2837_);
return v___x_2838_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2841_ = l_Lean_stringToMessageData(v___x_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2842_, lean_object* v_type_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_options_2849_; lean_object* v_inheritedTraceOptions_2850_; uint8_t v_hasTrace_2851_; uint8_t v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___f_2858_; lean_object* v___x_2859_; lean_object* v___f_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_options_2849_ = lean_ctor_get(v_a_2846_, 2);
v_inheritedTraceOptions_2850_ = lean_ctor_get(v_a_2846_, 13);
v_hasTrace_2851_ = lean_ctor_get_uint8(v_options_2849_, sizeof(void*)*1);
v___x_2852_ = 0;
lean_inc(v_declName_2842_);
v___x_2853_ = l_Lean_MessageData_ofConstName(v_declName_2842_, v___x_2852_);
v___x_2854_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
lean_ctor_set(v___x_2855_, 1, v___x_2853_);
v___x_2856_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___f_2858_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_2858_, 0, v___x_2857_);
v___x_2859_ = lean_box(0);
lean_inc_ref(v_type_2843_);
v___f_2860_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2860_, 0, v_type_2843_);
lean_closure_set(v___f_2860_, 1, v___x_2859_);
lean_closure_set(v___f_2860_, 2, v_declName_2842_);
v___x_2861_ = lean_box(v___x_2852_);
v___x_2862_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2862_, 0, lean_box(0));
lean_closure_set(v___x_2862_, 1, v___f_2860_);
lean_closure_set(v___x_2862_, 2, v___x_2861_);
if (v_hasTrace_2851_ == 0)
{
lean_object* v___x_2863_; 
lean_dec_ref(v_type_2843_);
v___x_2863_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2862_, v___f_2858_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
v_a_2872_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2863_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2863_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v___f_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v_a_2888_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v_a_2903_; 
v___f_2880_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2880_, 0, v_type_2843_);
v___x_2881_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_2882_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2883_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2884_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2850_, v_options_2849_, v___x_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = l_Lean_trace_profiler;
v___x_2954_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2849_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_object* v___x_2955_; 
lean_dec_ref(v___f_2880_);
v___x_2955_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2862_, v___f_2858_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2955_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2955_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v_a_2964_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2955_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2955_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
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
return v___x_2969_;
}
}
}
}
else
{
goto v___jp_2912_;
}
}
else
{
goto v___jp_2912_;
}
v___jp_2885_:
{
lean_object* v___x_2889_; double v___x_2890_; double v___x_2891_; double v___x_2892_; double v___x_2893_; double v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2889_ = lean_io_mono_nanos_now();
v___x_2890_ = lean_float_of_nat(v___y_2887_);
v___x_2891_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2892_ = lean_float_div(v___x_2890_, v___x_2891_);
v___x_2893_ = lean_float_of_nat(v___x_2889_);
v___x_2894_ = lean_float_div(v___x_2893_, v___x_2891_);
v___x_2895_ = lean_box_float(v___x_2892_);
v___x_2896_ = lean_box_float(v___x_2894_);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2895_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v_a_2888_);
lean_ctor_set(v___x_2898_, 1, v___x_2897_);
v___x_2899_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2881_, v_hasTrace_2851_, v___x_2882_, v_options_2849_, v___x_2884_, v___y_2886_, v___f_2880_, v___x_2898_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2899_;
}
v___jp_2900_:
{
lean_object* v___x_2904_; double v___x_2905_; double v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2904_ = lean_io_get_num_heartbeats();
v___x_2905_ = lean_float_of_nat(v___y_2902_);
v___x_2906_ = lean_float_of_nat(v___x_2904_);
v___x_2907_ = lean_box_float(v___x_2905_);
v___x_2908_ = lean_box_float(v___x_2906_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_a_2903_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2881_, v_hasTrace_2851_, v___x_2882_, v_options_2849_, v___x_2884_, v___y_2901_, v___f_2880_, v___x_2910_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
return v___x_2911_;
}
v___jp_2912_:
{
lean_object* v___x_2913_; lean_object* v_a_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2913_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2847_);
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2913_);
v___x_2915_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2916_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2849_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_io_mono_nanos_now();
v___x_2918_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2862_, v___f_2858_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2918_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2918_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set_tag(v___x_2921_, 1);
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
v___y_2886_ = v_a_2914_;
v___y_2887_ = v___x_2917_;
v_a_2888_ = v___x_2924_;
goto v___jp_2885_;
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
v_a_2927_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2918_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2918_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 0);
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
v___y_2886_ = v_a_2914_;
v___y_2887_ = v___x_2917_;
v_a_2888_ = v___x_2932_;
goto v___jp_2885_;
}
}
}
}
else
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_io_get_num_heartbeats();
v___x_2936_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2862_, v___f_2858_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
lean_ctor_set_tag(v___x_2939_, 1);
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
v___y_2901_ = v_a_2914_;
v___y_2902_ = v___x_2935_;
v_a_2903_ = v___x_2942_;
goto v___jp_2900_;
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2936_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2936_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 0);
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
v___y_2901_ = v_a_2914_;
v___y_2902_ = v___x_2935_;
v_a_2903_ = v___x_2950_;
goto v___jp_2900_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_2972_, lean_object* v_type_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_2972_, v_type_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_);
lean_dec(v_a_2977_);
lean_dec_ref(v_a_2976_);
lean_dec(v_a_2975_);
lean_dec_ref(v_a_2974_);
return v_res_2979_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_2980_, lean_object* v_n_2981_, lean_object* v_x_2982_){
_start:
{
uint8_t v___x_2983_; 
v___x_2983_ = l_Lean_Environment_hasExposedBody(v_env_2980_, v_n_2981_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_env_2984_, lean_object* v_n_2985_, lean_object* v_x_2986_){
_start:
{
uint8_t v_res_2987_; lean_object* v_r_2988_; 
v_res_2987_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(v_env_2984_, v_n_2985_, v_x_2986_);
lean_dec_ref(v_x_2986_);
v_r_2988_ = lean_box(v_res_2987_);
return v_r_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_2989_, lean_object* v_x_2990_){
_start:
{
if (lean_obj_tag(v_x_2990_) == 0)
{
lean_object* v_k_2991_; lean_object* v_v_2992_; lean_object* v_l_2993_; lean_object* v_r_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_k_2991_ = lean_ctor_get(v_x_2990_, 1);
v_v_2992_ = lean_ctor_get(v_x_2990_, 2);
v_l_2993_ = lean_ctor_get(v_x_2990_, 3);
v_r_2994_ = lean_ctor_get(v_x_2990_, 4);
v___x_2995_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_2989_, v_l_2993_);
lean_inc(v_v_2992_);
lean_inc(v_k_2991_);
v___x_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2996_, 0, v_k_2991_);
lean_ctor_set(v___x_2996_, 1, v_v_2992_);
v___x_2997_ = lean_array_push(v___x_2995_, v___x_2996_);
v_init_2989_ = v___x_2997_;
v_x_2990_ = v_r_2994_;
goto _start;
}
else
{
return v_init_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_2999_, v_x_3000_);
lean_dec(v_x_3000_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_3004_, lean_object* v_s_3005_){
_start:
{
lean_object* v___f_3006_; lean_object* v___x_3007_; lean_object* v_all_3008_; lean_object* v___x_3009_; lean_object* v_exported_3010_; lean_object* v___x_3011_; 
v___f_3006_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3006_, 0, v_env_3004_);
v___x_3007_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v_all_3008_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3007_, v_s_3005_);
v___x_3009_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3006_, v_s_3005_);
v_exported_3010_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3007_, v___x_3009_);
lean_dec(v___x_3009_);
lean_inc_ref(v_exported_3010_);
v___x_3011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3011_, 0, v_exported_3010_);
lean_ctor_set(v___x_3011_, 1, v_exported_3010_);
lean_ctor_set(v___x_3011_, 2, v_all_3008_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___f_3024_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3025_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3026_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3027_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3025_, v___x_3026_, v___f_3024_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_a_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_();
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(lean_object* v_init_3030_, lean_object* v_t_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3030_, v_t_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3033_, lean_object* v_t_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(v_init_3033_, v_t_3034_);
lean_dec(v_t_3034_);
return v_res_3035_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3036_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3041_, lean_object* v_declNames_3042_, lean_object* v_recArgPos_3043_, lean_object* v_fixedParamPerms_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v_levelParams_3048_; lean_object* v_declName_3049_; lean_object* v_type_3050_; lean_object* v_value_3051_; lean_object* v___x_3052_; 
v_levelParams_3048_ = lean_ctor_get(v_preDef_3041_, 1);
lean_inc(v_levelParams_3048_);
v_declName_3049_ = lean_ctor_get(v_preDef_3041_, 3);
lean_inc_n(v_declName_3049_, 2);
v_type_3050_ = lean_ctor_get(v_preDef_3041_, 6);
lean_inc_ref(v_type_3050_);
v_value_3051_ = lean_ctor_get(v_preDef_3041_, 7);
lean_inc_ref(v_value_3051_);
lean_dec_ref(v_preDef_3041_);
v___x_3052_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3049_, v_a_3045_, v_a_3046_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3082_; 
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v___x_3052_, 0);
lean_dec(v_unused_3083_);
v___x_3054_ = v___x_3052_;
v_isShared_3055_ = v_isSharedCheck_3082_;
goto v_resetjp_3053_;
}
else
{
lean_dec(v___x_3052_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3082_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v_env_3057_; lean_object* v_nextMacroScope_3058_; lean_object* v_ngen_3059_; lean_object* v_auxDeclNGen_3060_; lean_object* v_traceState_3061_; lean_object* v_messages_3062_; lean_object* v_infoState_3063_; lean_object* v_snapshotTasks_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3080_; 
v___x_3056_ = lean_st_ref_take(v_a_3046_);
v_env_3057_ = lean_ctor_get(v___x_3056_, 0);
v_nextMacroScope_3058_ = lean_ctor_get(v___x_3056_, 1);
v_ngen_3059_ = lean_ctor_get(v___x_3056_, 2);
v_auxDeclNGen_3060_ = lean_ctor_get(v___x_3056_, 3);
v_traceState_3061_ = lean_ctor_get(v___x_3056_, 4);
v_messages_3062_ = lean_ctor_get(v___x_3056_, 6);
v_infoState_3063_ = lean_ctor_get(v___x_3056_, 7);
v_snapshotTasks_3064_ = lean_ctor_get(v___x_3056_, 8);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v___x_3056_, 5);
lean_dec(v_unused_3081_);
v___x_3066_ = v___x_3056_;
v_isShared_3067_ = v_isSharedCheck_3080_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_snapshotTasks_3064_);
lean_inc(v_infoState_3063_);
lean_inc(v_messages_3062_);
lean_inc(v_traceState_3061_);
lean_inc(v_auxDeclNGen_3060_);
lean_inc(v_ngen_3059_);
lean_inc(v_nextMacroScope_3058_);
lean_inc(v_env_3057_);
lean_dec(v___x_3056_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3080_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3068_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3049_);
v___x_3069_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3069_, 0, v_declName_3049_);
lean_ctor_set(v___x_3069_, 1, v_levelParams_3048_);
lean_ctor_set(v___x_3069_, 2, v_type_3050_);
lean_ctor_set(v___x_3069_, 3, v_value_3051_);
lean_ctor_set(v___x_3069_, 4, v_recArgPos_3043_);
lean_ctor_set(v___x_3069_, 5, v_declNames_3042_);
lean_ctor_set(v___x_3069_, 6, v_fixedParamPerms_3044_);
v___x_3070_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3068_, v_env_3057_, v_declName_3049_, v___x_3069_);
v___x_3071_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 5, v___x_3071_);
lean_ctor_set(v___x_3066_, 0, v___x_3070_);
v___x_3073_ = v___x_3066_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v_nextMacroScope_3058_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_ngen_3059_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_auxDeclNGen_3060_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_traceState_3061_);
lean_ctor_set(v_reuseFailAlloc_3079_, 5, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3079_, 6, v_messages_3062_);
lean_ctor_set(v_reuseFailAlloc_3079_, 7, v_infoState_3063_);
lean_ctor_set(v_reuseFailAlloc_3079_, 8, v_snapshotTasks_3064_);
v___x_3073_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v___x_3074_ = lean_st_ref_set(v_a_3046_, v___x_3073_);
v___x_3075_ = lean_box(0);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3075_);
v___x_3077_ = v___x_3054_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
}
else
{
lean_dec_ref(v_value_3051_);
lean_dec_ref(v_type_3050_);
lean_dec(v_declName_3049_);
lean_dec(v_levelParams_3048_);
lean_dec_ref(v_fixedParamPerms_3044_);
lean_dec(v_recArgPos_3043_);
lean_dec_ref(v_declNames_3042_);
return v___x_3052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3084_, lean_object* v_declNames_3085_, lean_object* v_recArgPos_3086_, lean_object* v_fixedParamPerms_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3084_, v_declNames_3085_, v_recArgPos_3086_, v_fixedParamPerms_3087_, v_a_3088_, v_a_3089_);
lean_dec(v_a_3089_);
lean_dec_ref(v_a_3088_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3092_, lean_object* v_k_3093_, uint8_t v_cleanupAnnotations_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___f_3100_; uint8_t v___x_3101_; uint8_t v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___f_3100_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3100_, 0, v_k_3093_);
v___x_3101_ = 1;
v___x_3102_ = 0;
v___x_3103_ = lean_box(0);
v___x_3104_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3092_, v___x_3101_, v___x_3102_, v___x_3101_, v___x_3102_, v___x_3103_, v___f_3100_, v_cleanupAnnotations_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
else
{
lean_object* v_a_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3120_; 
v_a_3113_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3115_ = v___x_3104_;
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_a_3113_);
lean_dec(v___x_3104_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3120_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3118_; 
if (v_isShared_3116_ == 0)
{
v___x_3118_ = v___x_3115_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_a_3113_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3121_, lean_object* v_k_3122_, lean_object* v_cleanupAnnotations_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3129_; lean_object* v_res_3130_; 
v_cleanupAnnotations_boxed_3129_ = lean_unbox(v_cleanupAnnotations_3123_);
v_res_3130_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3121_, v_k_3122_, v_cleanupAnnotations_boxed_3129_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3131_, lean_object* v_e_3132_, lean_object* v_k_3133_, uint8_t v_cleanupAnnotations_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3132_, v_k_3133_, v_cleanupAnnotations_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3141_, lean_object* v_e_3142_, lean_object* v_k_3143_, lean_object* v_cleanupAnnotations_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3150_; lean_object* v_res_3151_; 
v_cleanupAnnotations_boxed_3150_ = lean_unbox(v_cleanupAnnotations_3144_);
v_res_3151_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3141_, v_e_3142_, v_k_3143_, v_cleanupAnnotations_boxed_3150_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3152_, uint8_t v_isExporting_3153_, lean_object* v___x_3154_, lean_object* v___y_3155_, lean_object* v___x_3156_, lean_object* v_a_x3f_3157_){
_start:
{
lean_object* v___x_3159_; lean_object* v_env_3160_; lean_object* v_nextMacroScope_3161_; lean_object* v_ngen_3162_; lean_object* v_auxDeclNGen_3163_; lean_object* v_traceState_3164_; lean_object* v_messages_3165_; lean_object* v_infoState_3166_; lean_object* v_snapshotTasks_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3192_; 
v___x_3159_ = lean_st_ref_take(v___y_3152_);
v_env_3160_ = lean_ctor_get(v___x_3159_, 0);
v_nextMacroScope_3161_ = lean_ctor_get(v___x_3159_, 1);
v_ngen_3162_ = lean_ctor_get(v___x_3159_, 2);
v_auxDeclNGen_3163_ = lean_ctor_get(v___x_3159_, 3);
v_traceState_3164_ = lean_ctor_get(v___x_3159_, 4);
v_messages_3165_ = lean_ctor_get(v___x_3159_, 6);
v_infoState_3166_ = lean_ctor_get(v___x_3159_, 7);
v_snapshotTasks_3167_ = lean_ctor_get(v___x_3159_, 8);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v___x_3159_, 5);
lean_dec(v_unused_3193_);
v___x_3169_ = v___x_3159_;
v_isShared_3170_ = v_isSharedCheck_3192_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_snapshotTasks_3167_);
lean_inc(v_infoState_3166_);
lean_inc(v_messages_3165_);
lean_inc(v_traceState_3164_);
lean_inc(v_auxDeclNGen_3163_);
lean_inc(v_ngen_3162_);
lean_inc(v_nextMacroScope_3161_);
lean_inc(v_env_3160_);
lean_dec(v___x_3159_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3192_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = l_Lean_Environment_setExporting(v_env_3160_, v_isExporting_3153_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 5, v___x_3154_);
lean_ctor_set(v___x_3169_, 0, v___x_3171_);
v___x_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_nextMacroScope_3161_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_ngen_3162_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_auxDeclNGen_3163_);
lean_ctor_set(v_reuseFailAlloc_3191_, 4, v_traceState_3164_);
lean_ctor_set(v_reuseFailAlloc_3191_, 5, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3191_, 6, v_messages_3165_);
lean_ctor_set(v_reuseFailAlloc_3191_, 7, v_infoState_3166_);
lean_ctor_set(v_reuseFailAlloc_3191_, 8, v_snapshotTasks_3167_);
v___x_3173_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v_mctx_3176_; lean_object* v_zetaDeltaFVarIds_3177_; lean_object* v_postponed_3178_; lean_object* v_diag_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3189_; 
v___x_3174_ = lean_st_ref_set(v___y_3152_, v___x_3173_);
v___x_3175_ = lean_st_ref_take(v___y_3155_);
v_mctx_3176_ = lean_ctor_get(v___x_3175_, 0);
v_zetaDeltaFVarIds_3177_ = lean_ctor_get(v___x_3175_, 2);
v_postponed_3178_ = lean_ctor_get(v___x_3175_, 3);
v_diag_3179_ = lean_ctor_get(v___x_3175_, 4);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v___x_3175_, 1);
lean_dec(v_unused_3190_);
v___x_3181_ = v___x_3175_;
v_isShared_3182_ = v_isSharedCheck_3189_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_diag_3179_);
lean_inc(v_postponed_3178_);
lean_inc(v_zetaDeltaFVarIds_3177_);
lean_inc(v_mctx_3176_);
lean_dec(v___x_3175_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3189_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 1, v___x_3156_);
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_mctx_3176_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v___x_3156_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_zetaDeltaFVarIds_3177_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_postponed_3178_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_diag_3179_);
v___x_3184_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3185_ = lean_st_ref_set(v___y_3155_, v___x_3184_);
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3194_, lean_object* v_isExporting_3195_, lean_object* v___x_3196_, lean_object* v___y_3197_, lean_object* v___x_3198_, lean_object* v_a_x3f_3199_, lean_object* v___y_3200_){
_start:
{
uint8_t v_isExporting_boxed_3201_; lean_object* v_res_3202_; 
v_isExporting_boxed_3201_ = lean_unbox(v_isExporting_3195_);
v_res_3202_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3194_, v_isExporting_boxed_3201_, v___x_3196_, v___y_3197_, v___x_3198_, v_a_x3f_3199_);
lean_dec(v_a_x3f_3199_);
lean_dec(v___y_3197_);
lean_dec(v___y_3194_);
return v_res_3202_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3204_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3203_);
lean_ctor_set(v___x_3204_, 2, v___x_3203_);
lean_ctor_set(v___x_3204_, 3, v___x_3203_);
lean_ctor_set(v___x_3204_, 4, v___x_3203_);
lean_ctor_set(v___x_3204_, 5, v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3205_, uint8_t v_isExporting_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___x_3212_; lean_object* v_env_3213_; uint8_t v_isExporting_3214_; lean_object* v___x_3215_; lean_object* v_env_3216_; lean_object* v_nextMacroScope_3217_; lean_object* v_ngen_3218_; lean_object* v_auxDeclNGen_3219_; lean_object* v_traceState_3220_; lean_object* v_messages_3221_; lean_object* v_infoState_3222_; lean_object* v_snapshotTasks_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3277_; 
v___x_3212_ = lean_st_ref_get(v___y_3210_);
v_env_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc_ref(v_env_3213_);
lean_dec(v___x_3212_);
v_isExporting_3214_ = lean_ctor_get_uint8(v_env_3213_, sizeof(void*)*8);
lean_dec_ref(v_env_3213_);
v___x_3215_ = lean_st_ref_take(v___y_3210_);
v_env_3216_ = lean_ctor_get(v___x_3215_, 0);
v_nextMacroScope_3217_ = lean_ctor_get(v___x_3215_, 1);
v_ngen_3218_ = lean_ctor_get(v___x_3215_, 2);
v_auxDeclNGen_3219_ = lean_ctor_get(v___x_3215_, 3);
v_traceState_3220_ = lean_ctor_get(v___x_3215_, 4);
v_messages_3221_ = lean_ctor_get(v___x_3215_, 6);
v_infoState_3222_ = lean_ctor_get(v___x_3215_, 7);
v_snapshotTasks_3223_ = lean_ctor_get(v___x_3215_, 8);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3277_ == 0)
{
lean_object* v_unused_3278_; 
v_unused_3278_ = lean_ctor_get(v___x_3215_, 5);
lean_dec(v_unused_3278_);
v___x_3225_ = v___x_3215_;
v_isShared_3226_ = v_isSharedCheck_3277_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_snapshotTasks_3223_);
lean_inc(v_infoState_3222_);
lean_inc(v_messages_3221_);
lean_inc(v_traceState_3220_);
lean_inc(v_auxDeclNGen_3219_);
lean_inc(v_ngen_3218_);
lean_inc(v_nextMacroScope_3217_);
lean_inc(v_env_3216_);
lean_dec(v___x_3215_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3277_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3227_ = l_Lean_Environment_setExporting(v_env_3216_, v_isExporting_3206_);
v___x_3228_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 5, v___x_3228_);
lean_ctor_set(v___x_3225_, 0, v___x_3227_);
v___x_3230_ = v___x_3225_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3276_, 1, v_nextMacroScope_3217_);
lean_ctor_set(v_reuseFailAlloc_3276_, 2, v_ngen_3218_);
lean_ctor_set(v_reuseFailAlloc_3276_, 3, v_auxDeclNGen_3219_);
lean_ctor_set(v_reuseFailAlloc_3276_, 4, v_traceState_3220_);
lean_ctor_set(v_reuseFailAlloc_3276_, 5, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3276_, 6, v_messages_3221_);
lean_ctor_set(v_reuseFailAlloc_3276_, 7, v_infoState_3222_);
lean_ctor_set(v_reuseFailAlloc_3276_, 8, v_snapshotTasks_3223_);
v___x_3230_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v_mctx_3233_; lean_object* v_zetaDeltaFVarIds_3234_; lean_object* v_postponed_3235_; lean_object* v_diag_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3274_; 
v___x_3231_ = lean_st_ref_set(v___y_3210_, v___x_3230_);
v___x_3232_ = lean_st_ref_take(v___y_3208_);
v_mctx_3233_ = lean_ctor_get(v___x_3232_, 0);
v_zetaDeltaFVarIds_3234_ = lean_ctor_get(v___x_3232_, 2);
v_postponed_3235_ = lean_ctor_get(v___x_3232_, 3);
v_diag_3236_ = lean_ctor_get(v___x_3232_, 4);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3274_ == 0)
{
lean_object* v_unused_3275_; 
v_unused_3275_ = lean_ctor_get(v___x_3232_, 1);
lean_dec(v_unused_3275_);
v___x_3238_ = v___x_3232_;
v_isShared_3239_ = v_isSharedCheck_3274_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_diag_3236_);
lean_inc(v_postponed_3235_);
lean_inc(v_zetaDeltaFVarIds_3234_);
lean_inc(v_mctx_3233_);
lean_dec(v___x_3232_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3274_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3240_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 1, v___x_3240_);
v___x_3242_ = v___x_3238_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3273_; 
v_reuseFailAlloc_3273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_mctx_3233_);
lean_ctor_set(v_reuseFailAlloc_3273_, 1, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3273_, 2, v_zetaDeltaFVarIds_3234_);
lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_postponed_3235_);
lean_ctor_set(v_reuseFailAlloc_3273_, 4, v_diag_3236_);
v___x_3242_ = v_reuseFailAlloc_3273_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v_r_3244_; 
v___x_3243_ = lean_st_ref_set(v___y_3208_, v___x_3242_);
lean_inc(v___y_3210_);
lean_inc_ref(v___y_3209_);
lean_inc(v___y_3208_);
lean_inc_ref(v___y_3207_);
v_r_3244_ = lean_apply_5(v_x_3205_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, lean_box(0));
if (lean_obj_tag(v_r_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3261_; 
v_a_3245_ = lean_ctor_get(v_r_3244_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v_r_3244_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3247_ = v_r_3244_;
v_isShared_3248_ = v_isSharedCheck_3261_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v_r_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3261_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
lean_inc(v_a_3245_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set_tag(v___x_3247_, 1);
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
v___x_3251_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3210_, v_isExporting_3214_, v___x_3228_, v___y_3208_, v___x_3240_, v___x_3250_);
lean_dec_ref(v___x_3250_);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v___x_3251_, 0);
lean_dec(v_unused_3259_);
v___x_3253_ = v___x_3251_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_dec(v___x_3251_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v_a_3245_);
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3245_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
v_a_3262_ = lean_ctor_get(v_r_3244_, 0);
lean_inc(v_a_3262_);
lean_dec_ref_known(v_r_3244_, 1);
v___x_3263_ = lean_box(0);
v___x_3264_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3210_, v_isExporting_3214_, v___x_3228_, v___y_3208_, v___x_3240_, v___x_3263_);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3271_ == 0)
{
lean_object* v_unused_3272_; 
v_unused_3272_ = lean_ctor_get(v___x_3264_, 0);
lean_dec(v_unused_3272_);
v___x_3266_ = v___x_3264_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_dec(v___x_3264_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
lean_ctor_set_tag(v___x_3266_, 1);
lean_ctor_set(v___x_3266_, 0, v_a_3262_);
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3262_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3279_, lean_object* v_isExporting_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_){
_start:
{
uint8_t v_isExporting_boxed_3286_; lean_object* v_res_3287_; 
v_isExporting_boxed_3286_ = lean_unbox(v_isExporting_3280_);
v_res_3287_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3279_, v_isExporting_boxed_3286_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3288_, uint8_t v_when_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
if (v_when_3289_ == 0)
{
lean_object* v___x_3295_; 
lean_inc(v___y_3293_);
lean_inc_ref(v___y_3292_);
lean_inc(v___y_3291_);
lean_inc_ref(v___y_3290_);
v___x_3295_ = lean_apply_5(v_x_3288_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, lean_box(0));
return v___x_3295_;
}
else
{
uint8_t v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = 0;
v___x_3297_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3288_, v___x_3296_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3298_, lean_object* v_when_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
uint8_t v_when_boxed_3305_; lean_object* v_res_3306_; 
v_when_boxed_3305_ = lean_unbox(v_when_3299_);
v_res_3306_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3298_, v_when_boxed_3305_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
if (lean_obj_tag(v_a_3307_) == 0)
{
lean_object* v___x_3309_; 
v___x_3309_ = l_List_reverse___redArg(v_a_3308_);
return v___x_3309_;
}
else
{
lean_object* v_head_3310_; lean_object* v_tail_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3320_; 
v_head_3310_ = lean_ctor_get(v_a_3307_, 0);
v_tail_3311_ = lean_ctor_get(v_a_3307_, 1);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_a_3307_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3313_ = v_a_3307_;
v_isShared_3314_ = v_isSharedCheck_3320_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_tail_3311_);
lean_inc(v_head_3310_);
lean_dec(v_a_3307_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3320_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3315_ = l_Lean_mkLevelParam(v_head_3310_);
if (v_isShared_3314_ == 0)
{
lean_ctor_set(v___x_3313_, 1, v_a_3308_);
lean_ctor_set(v___x_3313_, 0, v___x_3315_);
v___x_3317_ = v___x_3313_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3315_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_a_3308_);
v___x_3317_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
v_a_3307_ = v_tail_3311_;
v_a_3308_ = v___x_3317_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3321_, lean_object* v_declName_3322_, lean_object* v_name_3323_, lean_object* v_xs_3324_, lean_object* v_body_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; lean_object* v_us_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3331_ = lean_box(0);
lean_inc(v_levelParams_3321_);
v_us_3332_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3321_, v___x_3331_);
lean_inc(v_declName_3322_);
v___x_3333_ = l_Lean_mkConst(v_declName_3322_, v_us_3332_);
v___x_3334_ = l_Lean_mkAppN(v___x_3333_, v_xs_3324_);
v___x_3335_ = l_Lean_Meta_mkEq(v___x_3334_, v_body_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc_n(v_a_3336_, 2);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3337_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3337_, 0, v_declName_3322_);
lean_closure_set(v___x_3337_, 1, v_a_3336_);
v___x_3338_ = 1;
v___x_3339_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3337_, v___x_3338_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; uint8_t v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc(v_a_3340_);
lean_dec_ref_known(v___x_3339_, 1);
v___x_3341_ = 0;
v___x_3342_ = 1;
v___x_3343_ = l_Lean_Meta_mkForallFVars(v_xs_3324_, v_a_3336_, v___x_3341_, v___x_3338_, v___x_3338_, v___x_3342_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3345_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v___x_3345_ = l_Lean_Meta_letToHave(v_a_3344_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = l_Lean_Meta_mkLambdaFVars(v_xs_3324_, v_a_3340_, v___x_3341_, v___x_3338_, v___x_3341_, v___x_3338_, v___x_3342_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
lean_inc_n(v_name_3323_, 2);
v___x_3349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3349_, 0, v_name_3323_);
lean_ctor_set(v___x_3349_, 1, v_levelParams_3321_);
lean_ctor_set(v___x_3349_, 2, v_a_3346_);
v___x_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3350_, 0, v_name_3323_);
lean_ctor_set(v___x_3350_, 1, v___x_3331_);
v___x_3351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v_a_3348_);
lean_ctor_set(v___x_3351_, 2, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
v___x_3353_ = l_Lean_addDecl(v___x_3352_, v___x_3341_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v___x_3354_; 
lean_dec_ref_known(v___x_3353_, 1);
v___x_3354_ = l_Lean_inferDefEqAttr(v_name_3323_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3354_;
}
else
{
lean_dec(v_name_3323_);
return v___x_3353_;
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec(v_a_3346_);
lean_dec(v_name_3323_);
lean_dec(v_levelParams_3321_);
v_a_3355_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3347_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3347_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v_a_3340_);
lean_dec(v_name_3323_);
lean_dec(v_levelParams_3321_);
v_a_3363_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3345_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3345_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v_a_3340_);
lean_dec(v_name_3323_);
lean_dec(v_levelParams_3321_);
v_a_3371_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3343_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3343_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_a_3336_);
lean_dec(v_name_3323_);
lean_dec(v_levelParams_3321_);
v_a_3379_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3339_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3339_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_name_3323_);
lean_dec(v_declName_3322_);
lean_dec(v_levelParams_3321_);
v_a_3387_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3335_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3335_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3395_, lean_object* v_declName_3396_, lean_object* v_name_3397_, lean_object* v_xs_3398_, lean_object* v_body_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3395_, v_declName_3396_, v_name_3397_, v_xs_3398_, v_body_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v_xs_3398_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3406_, lean_object* v_k_3407_, uint8_t v_v_3408_){
_start:
{
lean_object* v_map_3409_; uint8_t v_hasTrace_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3424_; 
v_map_3409_ = lean_ctor_get(v_o_3406_, 0);
v_hasTrace_3410_ = lean_ctor_get_uint8(v_o_3406_, sizeof(void*)*1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_o_3406_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3412_ = v_o_3406_;
v_isShared_3413_ = v_isSharedCheck_3424_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_map_3409_);
lean_dec(v_o_3406_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3424_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3414_, 0, v_v_3408_);
lean_inc(v_k_3407_);
v___x_3415_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3407_, v___x_3414_, v_map_3409_);
if (v_hasTrace_3410_ == 0)
{
lean_object* v___x_3416_; uint8_t v___x_3417_; lean_object* v___x_3419_; 
v___x_3416_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3417_ = l_Lean_Name_isPrefixOf(v___x_3416_, v_k_3407_);
lean_dec(v_k_3407_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3415_);
v___x_3419_ = v___x_3412_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3415_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_ctor_set_uint8(v___x_3419_, sizeof(void*)*1, v___x_3417_);
return v___x_3419_;
}
}
else
{
lean_object* v___x_3422_; 
lean_dec(v_k_3407_);
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v___x_3415_);
v___x_3422_ = v___x_3412_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3415_);
lean_ctor_set_uint8(v_reuseFailAlloc_3423_, sizeof(void*)*1, v_hasTrace_3410_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3425_, lean_object* v_k_3426_, lean_object* v_v_3427_){
_start:
{
uint8_t v_v_boxed_3428_; lean_object* v_res_3429_; 
v_v_boxed_3428_ = lean_unbox(v_v_3427_);
v_res_3429_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3425_, v_k_3426_, v_v_boxed_3428_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3430_, lean_object* v_opt_3431_, uint8_t v_val_3432_){
_start:
{
lean_object* v_name_3433_; lean_object* v___x_3434_; 
v_name_3433_ = lean_ctor_get(v_opt_3431_, 0);
lean_inc(v_name_3433_);
lean_dec_ref(v_opt_3431_);
v___x_3434_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3430_, v_name_3433_, v_val_3432_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3435_, lean_object* v_opt_3436_, lean_object* v_val_3437_){
_start:
{
uint8_t v_val_boxed_3438_; lean_object* v_res_3439_; 
v_val_boxed_3438_ = lean_unbox(v_val_3437_);
v_res_3439_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3435_, v_opt_3436_, v_val_boxed_3438_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3440_, lean_object* v_info_3441_, lean_object* v_name_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v_levelParams_3449_; lean_object* v_value_3450_; lean_object* v_fileName_3451_; lean_object* v_fileMap_3452_; lean_object* v_options_3453_; lean_object* v_currRecDepth_3454_; lean_object* v_ref_3455_; lean_object* v_currNamespace_3456_; lean_object* v_openDecls_3457_; lean_object* v_initHeartbeats_3458_; lean_object* v_maxHeartbeats_3459_; lean_object* v_quotContext_3460_; lean_object* v_currMacroScope_3461_; lean_object* v_cancelTk_x3f_3462_; uint8_t v_suppressElabErrors_3463_; lean_object* v_inheritedTraceOptions_3464_; lean_object* v_env_3465_; lean_object* v___f_3466_; uint8_t v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; lean_object* v_fileName_3473_; lean_object* v_fileMap_3474_; lean_object* v_currRecDepth_3475_; lean_object* v_ref_3476_; lean_object* v_currNamespace_3477_; lean_object* v_openDecls_3478_; lean_object* v_initHeartbeats_3479_; lean_object* v_maxHeartbeats_3480_; lean_object* v_quotContext_3481_; lean_object* v_currMacroScope_3482_; lean_object* v_cancelTk_x3f_3483_; uint8_t v_suppressElabErrors_3484_; lean_object* v_inheritedTraceOptions_3485_; lean_object* v___y_3486_; uint8_t v___y_3492_; uint8_t v___x_3513_; 
v___x_3448_ = lean_st_ref_get(v_a_3446_);
v_levelParams_3449_ = lean_ctor_get(v_info_3441_, 1);
lean_inc(v_levelParams_3449_);
v_value_3450_ = lean_ctor_get(v_info_3441_, 3);
lean_inc_ref(v_value_3450_);
lean_dec_ref(v_info_3441_);
v_fileName_3451_ = lean_ctor_get(v_a_3445_, 0);
v_fileMap_3452_ = lean_ctor_get(v_a_3445_, 1);
v_options_3453_ = lean_ctor_get(v_a_3445_, 2);
v_currRecDepth_3454_ = lean_ctor_get(v_a_3445_, 3);
v_ref_3455_ = lean_ctor_get(v_a_3445_, 5);
v_currNamespace_3456_ = lean_ctor_get(v_a_3445_, 6);
v_openDecls_3457_ = lean_ctor_get(v_a_3445_, 7);
v_initHeartbeats_3458_ = lean_ctor_get(v_a_3445_, 8);
v_maxHeartbeats_3459_ = lean_ctor_get(v_a_3445_, 9);
v_quotContext_3460_ = lean_ctor_get(v_a_3445_, 10);
v_currMacroScope_3461_ = lean_ctor_get(v_a_3445_, 11);
v_cancelTk_x3f_3462_ = lean_ctor_get(v_a_3445_, 12);
v_suppressElabErrors_3463_ = lean_ctor_get_uint8(v_a_3445_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3464_ = lean_ctor_get(v_a_3445_, 13);
v_env_3465_ = lean_ctor_get(v___x_3448_, 0);
lean_inc_ref(v_env_3465_);
lean_dec(v___x_3448_);
v___f_3466_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3466_, 0, v_levelParams_3449_);
lean_closure_set(v___f_3466_, 1, v_declName_3440_);
lean_closure_set(v___f_3466_, 2, v_name_3442_);
v___x_3467_ = 0;
v___x_3468_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3453_);
v___x_3469_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3453_, v___x_3468_, v___x_3467_);
v___x_3470_ = l_Lean_diagnostics;
v___x_3471_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v___x_3469_, v___x_3470_);
v___x_3513_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3465_);
lean_dec_ref(v_env_3465_);
if (v___x_3513_ == 0)
{
if (v___x_3471_ == 0)
{
v_fileName_3473_ = v_fileName_3451_;
v_fileMap_3474_ = v_fileMap_3452_;
v_currRecDepth_3475_ = v_currRecDepth_3454_;
v_ref_3476_ = v_ref_3455_;
v_currNamespace_3477_ = v_currNamespace_3456_;
v_openDecls_3478_ = v_openDecls_3457_;
v_initHeartbeats_3479_ = v_initHeartbeats_3458_;
v_maxHeartbeats_3480_ = v_maxHeartbeats_3459_;
v_quotContext_3481_ = v_quotContext_3460_;
v_currMacroScope_3482_ = v_currMacroScope_3461_;
v_cancelTk_x3f_3483_ = v_cancelTk_x3f_3462_;
v_suppressElabErrors_3484_ = v_suppressElabErrors_3463_;
v_inheritedTraceOptions_3485_ = v_inheritedTraceOptions_3464_;
v___y_3486_ = v_a_3446_;
goto v___jp_3472_;
}
else
{
v___y_3492_ = v___x_3513_;
goto v___jp_3491_;
}
}
else
{
v___y_3492_ = v___x_3471_;
goto v___jp_3491_;
}
v___jp_3472_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3487_ = l_Lean_maxRecDepth;
v___x_3488_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___x_3469_, v___x_3487_);
lean_inc_ref(v_inheritedTraceOptions_3485_);
lean_inc(v_cancelTk_x3f_3483_);
lean_inc(v_currMacroScope_3482_);
lean_inc(v_quotContext_3481_);
lean_inc(v_maxHeartbeats_3480_);
lean_inc(v_initHeartbeats_3479_);
lean_inc(v_openDecls_3478_);
lean_inc(v_currNamespace_3477_);
lean_inc(v_ref_3476_);
lean_inc(v_currRecDepth_3475_);
lean_inc_ref(v_fileMap_3474_);
lean_inc_ref(v_fileName_3473_);
v___x_3489_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3489_, 0, v_fileName_3473_);
lean_ctor_set(v___x_3489_, 1, v_fileMap_3474_);
lean_ctor_set(v___x_3489_, 2, v___x_3469_);
lean_ctor_set(v___x_3489_, 3, v_currRecDepth_3475_);
lean_ctor_set(v___x_3489_, 4, v___x_3488_);
lean_ctor_set(v___x_3489_, 5, v_ref_3476_);
lean_ctor_set(v___x_3489_, 6, v_currNamespace_3477_);
lean_ctor_set(v___x_3489_, 7, v_openDecls_3478_);
lean_ctor_set(v___x_3489_, 8, v_initHeartbeats_3479_);
lean_ctor_set(v___x_3489_, 9, v_maxHeartbeats_3480_);
lean_ctor_set(v___x_3489_, 10, v_quotContext_3481_);
lean_ctor_set(v___x_3489_, 11, v_currMacroScope_3482_);
lean_ctor_set(v___x_3489_, 12, v_cancelTk_x3f_3483_);
lean_ctor_set(v___x_3489_, 13, v_inheritedTraceOptions_3485_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*14, v___x_3471_);
lean_ctor_set_uint8(v___x_3489_, sizeof(void*)*14 + 1, v_suppressElabErrors_3484_);
v___x_3490_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3450_, v___f_3466_, v___x_3467_, v_a_3443_, v_a_3444_, v___x_3489_, v___y_3486_);
lean_dec_ref_known(v___x_3489_, 14);
return v___x_3490_;
}
v___jp_3491_:
{
if (v___y_3492_ == 0)
{
lean_object* v___x_3493_; lean_object* v_env_3494_; lean_object* v_nextMacroScope_3495_; lean_object* v_ngen_3496_; lean_object* v_auxDeclNGen_3497_; lean_object* v_traceState_3498_; lean_object* v_messages_3499_; lean_object* v_infoState_3500_; lean_object* v_snapshotTasks_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3511_; 
v___x_3493_ = lean_st_ref_take(v_a_3446_);
v_env_3494_ = lean_ctor_get(v___x_3493_, 0);
v_nextMacroScope_3495_ = lean_ctor_get(v___x_3493_, 1);
v_ngen_3496_ = lean_ctor_get(v___x_3493_, 2);
v_auxDeclNGen_3497_ = lean_ctor_get(v___x_3493_, 3);
v_traceState_3498_ = lean_ctor_get(v___x_3493_, 4);
v_messages_3499_ = lean_ctor_get(v___x_3493_, 6);
v_infoState_3500_ = lean_ctor_get(v___x_3493_, 7);
v_snapshotTasks_3501_ = lean_ctor_get(v___x_3493_, 8);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3511_ == 0)
{
lean_object* v_unused_3512_; 
v_unused_3512_ = lean_ctor_get(v___x_3493_, 5);
lean_dec(v_unused_3512_);
v___x_3503_ = v___x_3493_;
v_isShared_3504_ = v_isSharedCheck_3511_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snapshotTasks_3501_);
lean_inc(v_infoState_3500_);
lean_inc(v_messages_3499_);
lean_inc(v_traceState_3498_);
lean_inc(v_auxDeclNGen_3497_);
lean_inc(v_ngen_3496_);
lean_inc(v_nextMacroScope_3495_);
lean_inc(v_env_3494_);
lean_dec(v___x_3493_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3511_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
v___x_3505_ = l_Lean_Kernel_enableDiag(v_env_3494_, v___x_3471_);
v___x_3506_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 5, v___x_3506_);
lean_ctor_set(v___x_3503_, 0, v___x_3505_);
v___x_3508_ = v___x_3503_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v___x_3505_);
lean_ctor_set(v_reuseFailAlloc_3510_, 1, v_nextMacroScope_3495_);
lean_ctor_set(v_reuseFailAlloc_3510_, 2, v_ngen_3496_);
lean_ctor_set(v_reuseFailAlloc_3510_, 3, v_auxDeclNGen_3497_);
lean_ctor_set(v_reuseFailAlloc_3510_, 4, v_traceState_3498_);
lean_ctor_set(v_reuseFailAlloc_3510_, 5, v___x_3506_);
lean_ctor_set(v_reuseFailAlloc_3510_, 6, v_messages_3499_);
lean_ctor_set(v_reuseFailAlloc_3510_, 7, v_infoState_3500_);
lean_ctor_set(v_reuseFailAlloc_3510_, 8, v_snapshotTasks_3501_);
v___x_3508_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3509_; 
v___x_3509_ = lean_st_ref_set(v_a_3446_, v___x_3508_);
v_fileName_3473_ = v_fileName_3451_;
v_fileMap_3474_ = v_fileMap_3452_;
v_currRecDepth_3475_ = v_currRecDepth_3454_;
v_ref_3476_ = v_ref_3455_;
v_currNamespace_3477_ = v_currNamespace_3456_;
v_openDecls_3478_ = v_openDecls_3457_;
v_initHeartbeats_3479_ = v_initHeartbeats_3458_;
v_maxHeartbeats_3480_ = v_maxHeartbeats_3459_;
v_quotContext_3481_ = v_quotContext_3460_;
v_currMacroScope_3482_ = v_currMacroScope_3461_;
v_cancelTk_x3f_3483_ = v_cancelTk_x3f_3462_;
v_suppressElabErrors_3484_ = v_suppressElabErrors_3463_;
v_inheritedTraceOptions_3485_ = v_inheritedTraceOptions_3464_;
v___y_3486_ = v_a_3446_;
goto v___jp_3472_;
}
}
}
else
{
v_fileName_3473_ = v_fileName_3451_;
v_fileMap_3474_ = v_fileMap_3452_;
v_currRecDepth_3475_ = v_currRecDepth_3454_;
v_ref_3476_ = v_ref_3455_;
v_currNamespace_3477_ = v_currNamespace_3456_;
v_openDecls_3478_ = v_openDecls_3457_;
v_initHeartbeats_3479_ = v_initHeartbeats_3458_;
v_maxHeartbeats_3480_ = v_maxHeartbeats_3459_;
v_quotContext_3481_ = v_quotContext_3460_;
v_currMacroScope_3482_ = v_currMacroScope_3461_;
v_cancelTk_x3f_3483_ = v_cancelTk_x3f_3462_;
v_suppressElabErrors_3484_ = v_suppressElabErrors_3463_;
v_inheritedTraceOptions_3485_ = v_inheritedTraceOptions_3464_;
v___y_3486_ = v_a_3446_;
goto v___jp_3472_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3514_, lean_object* v_info_3515_, lean_object* v_name_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3514_, v_info_3515_, v_name_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3523_, lean_object* v_x_3524_, uint8_t v_isExporting_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3524_, v_isExporting_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3532_, lean_object* v_x_3533_, lean_object* v_isExporting_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
uint8_t v_isExporting_boxed_3540_; lean_object* v_res_3541_; 
v_isExporting_boxed_3540_ = lean_unbox(v_isExporting_3534_);
v_res_3541_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3532_, v_x_3533_, v_isExporting_boxed_3540_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3542_, lean_object* v_x_3543_, uint8_t v_when_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3543_, v_when_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3551_, lean_object* v_x_3552_, lean_object* v_when_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
uint8_t v_when_boxed_3559_; lean_object* v_res_3560_; 
v_when_boxed_3559_ = lean_unbox(v_when_3553_);
v_res_3560_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3551_, v_x_3552_, v_when_boxed_3559_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3561_, lean_object* v_info_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v___x_3568_; lean_object* v_env_3569_; lean_object* v_declName_3570_; lean_object* v_declNames_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3568_ = lean_st_ref_get(v_a_3566_);
v_env_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc_ref(v_env_3569_);
lean_dec(v___x_3568_);
v_declName_3570_ = lean_ctor_get(v_info_3562_, 0);
v_declNames_3571_ = lean_ctor_get(v_info_3562_, 5);
v___x_3572_ = lean_box(0);
v___x_3573_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3570_);
v___x_3574_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3569_, v_declName_3570_, v___x_3573_);
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = lean_array_get(v___x_3572_, v_declNames_3571_, v___x_3575_);
lean_inc_n(v___x_3574_, 2);
lean_inc(v_declName_3561_);
v___x_3577_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3577_, 0, v_declName_3561_);
lean_closure_set(v___x_3577_, 1, v_info_3562_);
lean_closure_set(v___x_3577_, 2, v___x_3574_);
v___x_3578_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3578_, 0, lean_box(0));
lean_closure_set(v___x_3578_, 1, v_declName_3561_);
lean_closure_set(v___x_3578_, 2, v___x_3577_);
v___x_3579_ = l_Lean_Meta_realizeConst(v___x_3576_, v___x_3574_, v___x_3578_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v___x_3579_, 0);
lean_dec(v_unused_3587_);
v___x_3581_ = v___x_3579_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_dec(v___x_3579_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set(v___x_3581_, 0, v___x_3574_);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3574_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v___x_3574_);
v_a_3588_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3579_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3579_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3596_, lean_object* v_info_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v_res_3603_; 
v_res_3603_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3596_, v_info_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v_env_3611_; lean_object* v___x_3612_; lean_object* v_toEnvExtension_3613_; lean_object* v_asyncMode_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3610_ = lean_st_ref_get(v_a_3608_);
v_env_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc_ref(v_env_3611_);
lean_dec(v___x_3610_);
v___x_3612_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3613_ = lean_ctor_get(v___x_3612_, 0);
v_asyncMode_3614_ = lean_ctor_get(v_toEnvExtension_3613_, 2);
v___x_3615_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3616_ = 0;
lean_inc(v_declName_3604_);
v___x_3617_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3615_, v___x_3612_, v_env_3611_, v_declName_3604_, v_asyncMode_3614_, v___x_3616_);
if (lean_obj_tag(v___x_3617_) == 1)
{
lean_object* v_val_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3642_; 
v_val_3618_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3620_ = v___x_3617_;
v_isShared_3621_ = v_isSharedCheck_3642_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_val_3618_);
lean_dec(v___x_3617_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3642_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; 
v___x_3622_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3604_, v_val_3618_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3633_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3625_ = v___x_3622_;
v_isShared_3626_ = v_isSharedCheck_3633_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3622_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3633_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v_a_3623_);
v___x_3628_ = v___x_3620_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
lean_object* v___x_3630_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v___x_3628_);
v___x_3630_ = v___x_3625_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
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
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_del_object(v___x_3620_);
v_a_3634_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3622_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3622_);
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
}
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec(v___x_3617_);
lean_dec(v_declName_3604_);
v___x_3643_ = lean_box(0);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
lean_dec(v_a_3649_);
lean_dec_ref(v_a_3648_);
lean_dec(v_a_3647_);
lean_dec_ref(v_a_3646_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v_env_3656_; lean_object* v___x_3657_; lean_object* v_toEnvExtension_3658_; lean_object* v_asyncMode_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; lean_object* v___x_3662_; 
v___x_3655_ = lean_st_ref_get(v_a_3653_);
v_env_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc_ref(v_env_3656_);
lean_dec(v___x_3655_);
v___x_3657_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3658_ = lean_ctor_get(v___x_3657_, 0);
v_asyncMode_3659_ = lean_ctor_get(v_toEnvExtension_3658_, 2);
v___x_3660_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3661_ = 0;
v___x_3662_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3660_, v___x_3657_, v_env_3656_, v_declName_3652_, v_asyncMode_3659_, v___x_3661_);
if (lean_obj_tag(v___x_3662_) == 1)
{
lean_object* v_val_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3672_; 
v_val_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3672_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3672_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_val_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3672_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v_recArgPos_3667_; lean_object* v___x_3669_; 
v_recArgPos_3667_ = lean_ctor_get(v_val_3663_, 4);
lean_inc(v_recArgPos_3667_);
lean_dec(v_val_3663_);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v_recArgPos_3667_);
v___x_3669_ = v___x_3665_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_recArgPos_3667_);
v___x_3669_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
return v___x_3670_;
}
}
}
else
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
lean_dec(v___x_3662_);
v___x_3673_ = lean_box(0);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
return v___x_3674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3675_, v_a_3676_);
lean_dec(v_a_3676_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v___x_3683_; 
lean_dec_ref(v_a_3680_);
v___x_3683_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3679_, v_a_3681_);
lean_dec(v_a_3681_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = lean_get_structural_rec_arg_pos(v_declName_3684_, v_a_3685_, v_a_3686_);
return v_res_3688_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3746_ = lean_unsigned_to_nat(2295916746u);
v___x_3747_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3748_ = l_Lean_Name_num___override(v___x_3747_, v___x_3746_);
return v___x_3748_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3750_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3751_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3752_ = l_Lean_Name_str___override(v___x_3751_, v___x_3750_);
return v___x_3752_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3754_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3755_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3756_ = l_Lean_Name_str___override(v___x_3755_, v___x_3754_);
return v___x_3756_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3757_ = lean_unsigned_to_nat(2u);
v___x_3758_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3759_ = l_Lean_Name_num___override(v___x_3758_, v___x_3757_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3762_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3761_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v___x_3763_; uint8_t v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_dec_ref_known(v___x_3762_, 1);
v___x_3763_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_3764_ = 0;
v___x_3765_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3766_ = l_Lean_registerTraceClass(v___x_3763_, v___x_3764_, v___x_3765_);
return v___x_3766_;
}
else
{
return v___x_3762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_3768_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
