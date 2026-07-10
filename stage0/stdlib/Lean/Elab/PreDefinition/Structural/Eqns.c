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
lean_object* lean_st_ref_get(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "step:\n"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 73, 239, 7, 229, 151, 237, 199)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 150, 182, 177, 14, 34, 156, 192)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "whnfReducibleLHS succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "simpMatch\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "simpIf\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14;
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "simpTargetStar closed the goal"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deltaRHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "casesOnStuckLHS\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "splitTarget\? succeeded"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "no progress at goal\n"};
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
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 232, 160, 88, 66, 78, 213, 243)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 14, 83, 143, 58, 41, 180, 194)}};
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_765_ = ((size_t)5ULL);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_unsigned_to_nat(32u);
v___x_768_ = lean_mk_empty_array_with_capacity(v___x_767_);
v___x_769_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__0);
v___x_770_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_770_, 0, v___x_769_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
lean_ctor_set(v___x_770_, 2, v___x_766_);
lean_ctor_set(v___x_770_, 3, v___x_766_);
lean_ctor_set_usize(v___x_770_, 4, v___x_765_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(lean_object* v___y_771_){
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
v___x_793_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg___boxed(lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v___y_805_);
lean_dec(v___y_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v___y_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v___y_814_, v___y_815_, v___y_816_, v___y_817_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
return v_res_819_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_opts_820_, lean_object* v_opt_821_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_opts_830_, lean_object* v_opt_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_opts_830_, v_opt_831_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_a_873_ = lean_ctor_get(v_x_871_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v_x_871_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v_x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v_x_871_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_x_871_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v_x_871_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v_x_871_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg___boxed(lean_object* v_x_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(v_x_889_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(lean_object* v_opts_892_, lean_object* v_opt_893_){
_start:
{
lean_object* v_name_894_; lean_object* v_defValue_895_; lean_object* v_map_896_; lean_object* v___x_897_; 
v_name_894_ = lean_ctor_get(v_opt_893_, 0);
v_defValue_895_ = lean_ctor_get(v_opt_893_, 1);
v_map_896_ = lean_ctor_get(v_opts_892_, 0);
v___x_897_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_896_, v_name_894_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_inc(v_defValue_895_);
return v_defValue_895_;
}
else
{
lean_object* v_val_898_; 
v_val_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v___x_897_, 1);
if (lean_obj_tag(v_val_898_) == 3)
{
lean_object* v_v_899_; 
v_v_899_ = lean_ctor_get(v_val_898_, 0);
lean_inc(v_v_899_);
lean_dec_ref_known(v_val_898_, 1);
return v_v_899_;
}
else
{
lean_dec(v_val_898_);
lean_inc(v_defValue_895_);
return v_defValue_895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5___boxed(lean_object* v_opts_900_, lean_object* v_opt_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(v_opts_900_, v_opt_901_);
lean_dec_ref(v_opt_901_);
lean_dec_ref(v_opts_900_);
return v_res_902_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__4(lean_object* v_e_903_){
_start:
{
if (lean_obj_tag(v_e_903_) == 0)
{
uint8_t v___x_904_; 
v___x_904_ = 2;
return v___x_904_;
}
else
{
uint8_t v___x_905_; 
v___x_905_ = 0;
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__4___boxed(lean_object* v_e_906_){
_start:
{
uint8_t v_res_907_; lean_object* v_r_908_; 
v_res_907_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__4(v_e_906_);
lean_dec_ref(v_e_906_);
v_r_908_ = lean_box(v_res_907_);
return v_r_908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2_spec__3(size_t v_sz_909_, size_t v_i_910_, lean_object* v_bs_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_lt(v_i_910_, v_sz_909_);
if (v___x_912_ == 0)
{
return v_bs_911_;
}
else
{
lean_object* v_v_913_; lean_object* v_msg_914_; lean_object* v___x_915_; lean_object* v_bs_x27_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
v_v_913_ = lean_array_uget_borrowed(v_bs_911_, v_i_910_);
v_msg_914_ = lean_ctor_get(v_v_913_, 1);
lean_inc_ref(v_msg_914_);
v___x_915_ = lean_unsigned_to_nat(0u);
v_bs_x27_916_ = lean_array_uset(v_bs_911_, v_i_910_, v___x_915_);
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_add(v_i_910_, v___x_917_);
v___x_919_ = lean_array_uset(v_bs_x27_916_, v_i_910_, v_msg_914_);
v_i_910_ = v___x_918_;
v_bs_911_ = v___x_919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_921_, lean_object* v_i_922_, lean_object* v_bs_923_){
_start:
{
size_t v_sz_boxed_924_; size_t v_i_boxed_925_; lean_object* v_res_926_; 
v_sz_boxed_924_ = lean_unbox_usize(v_sz_921_);
lean_dec(v_sz_921_);
v_i_boxed_925_ = lean_unbox_usize(v_i_922_);
lean_dec(v_i_922_);
v_res_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2_spec__3(v_sz_boxed_924_, v_i_boxed_925_, v_bs_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2(lean_object* v_oldTraces_927_, lean_object* v_data_928_, lean_object* v_ref_929_, lean_object* v_msg_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_fileName_936_; lean_object* v_fileMap_937_; lean_object* v_options_938_; lean_object* v_currRecDepth_939_; lean_object* v_maxRecDepth_940_; lean_object* v_ref_941_; lean_object* v_currNamespace_942_; lean_object* v_openDecls_943_; lean_object* v_initHeartbeats_944_; lean_object* v_maxHeartbeats_945_; lean_object* v_quotContext_946_; lean_object* v_currMacroScope_947_; uint8_t v_diag_948_; lean_object* v_cancelTk_x3f_949_; uint8_t v_suppressElabErrors_950_; lean_object* v_inheritedTraceOptions_951_; lean_object* v___x_952_; lean_object* v_traceState_953_; lean_object* v_traces_954_; lean_object* v_ref_955_; lean_object* v___x_956_; lean_object* v___x_957_; size_t v_sz_958_; size_t v___x_959_; lean_object* v___x_960_; lean_object* v_msg_961_; lean_object* v___x_962_; lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1000_; 
v_fileName_936_ = lean_ctor_get(v___y_933_, 0);
v_fileMap_937_ = lean_ctor_get(v___y_933_, 1);
v_options_938_ = lean_ctor_get(v___y_933_, 2);
v_currRecDepth_939_ = lean_ctor_get(v___y_933_, 3);
v_maxRecDepth_940_ = lean_ctor_get(v___y_933_, 4);
v_ref_941_ = lean_ctor_get(v___y_933_, 5);
v_currNamespace_942_ = lean_ctor_get(v___y_933_, 6);
v_openDecls_943_ = lean_ctor_get(v___y_933_, 7);
v_initHeartbeats_944_ = lean_ctor_get(v___y_933_, 8);
v_maxHeartbeats_945_ = lean_ctor_get(v___y_933_, 9);
v_quotContext_946_ = lean_ctor_get(v___y_933_, 10);
v_currMacroScope_947_ = lean_ctor_get(v___y_933_, 11);
v_diag_948_ = lean_ctor_get_uint8(v___y_933_, sizeof(void*)*14);
v_cancelTk_x3f_949_ = lean_ctor_get(v___y_933_, 12);
v_suppressElabErrors_950_ = lean_ctor_get_uint8(v___y_933_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_951_ = lean_ctor_get(v___y_933_, 13);
v___x_952_ = lean_st_ref_get(v___y_934_);
v_traceState_953_ = lean_ctor_get(v___x_952_, 4);
lean_inc_ref(v_traceState_953_);
lean_dec(v___x_952_);
v_traces_954_ = lean_ctor_get(v_traceState_953_, 0);
lean_inc_ref(v_traces_954_);
lean_dec_ref(v_traceState_953_);
v_ref_955_ = l_Lean_replaceRef(v_ref_929_, v_ref_941_);
lean_inc_ref(v_inheritedTraceOptions_951_);
lean_inc(v_cancelTk_x3f_949_);
lean_inc(v_currMacroScope_947_);
lean_inc(v_quotContext_946_);
lean_inc(v_maxHeartbeats_945_);
lean_inc(v_initHeartbeats_944_);
lean_inc(v_openDecls_943_);
lean_inc(v_currNamespace_942_);
lean_inc(v_maxRecDepth_940_);
lean_inc(v_currRecDepth_939_);
lean_inc_ref(v_options_938_);
lean_inc_ref(v_fileMap_937_);
lean_inc_ref(v_fileName_936_);
v___x_956_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_956_, 0, v_fileName_936_);
lean_ctor_set(v___x_956_, 1, v_fileMap_937_);
lean_ctor_set(v___x_956_, 2, v_options_938_);
lean_ctor_set(v___x_956_, 3, v_currRecDepth_939_);
lean_ctor_set(v___x_956_, 4, v_maxRecDepth_940_);
lean_ctor_set(v___x_956_, 5, v_ref_955_);
lean_ctor_set(v___x_956_, 6, v_currNamespace_942_);
lean_ctor_set(v___x_956_, 7, v_openDecls_943_);
lean_ctor_set(v___x_956_, 8, v_initHeartbeats_944_);
lean_ctor_set(v___x_956_, 9, v_maxHeartbeats_945_);
lean_ctor_set(v___x_956_, 10, v_quotContext_946_);
lean_ctor_set(v___x_956_, 11, v_currMacroScope_947_);
lean_ctor_set(v___x_956_, 12, v_cancelTk_x3f_949_);
lean_ctor_set(v___x_956_, 13, v_inheritedTraceOptions_951_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*14, v_diag_948_);
lean_ctor_set_uint8(v___x_956_, sizeof(void*)*14 + 1, v_suppressElabErrors_950_);
v___x_957_ = l_Lean_PersistentArray_toArray___redArg(v_traces_954_);
lean_dec_ref(v_traces_954_);
v_sz_958_ = lean_array_size(v___x_957_);
v___x_959_ = ((size_t)0ULL);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2_spec__3(v_sz_958_, v___x_959_, v___x_957_);
v_msg_961_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_961_, 0, v_data_928_);
lean_ctor_set(v_msg_961_, 1, v_msg_930_);
lean_ctor_set(v_msg_961_, 2, v___x_960_);
v___x_962_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_961_, v___y_931_, v___y_932_, v___x_956_, v___y_934_);
lean_dec_ref_known(v___x_956_, 14);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_1000_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1000_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v_traceState_968_; lean_object* v_env_969_; lean_object* v_nextMacroScope_970_; lean_object* v_ngen_971_; lean_object* v_auxDeclNGen_972_; lean_object* v_cache_973_; lean_object* v_messages_974_; lean_object* v_infoState_975_; lean_object* v_snapshotTasks_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_999_; 
v___x_967_ = lean_st_ref_take(v___y_934_);
v_traceState_968_ = lean_ctor_get(v___x_967_, 4);
v_env_969_ = lean_ctor_get(v___x_967_, 0);
v_nextMacroScope_970_ = lean_ctor_get(v___x_967_, 1);
v_ngen_971_ = lean_ctor_get(v___x_967_, 2);
v_auxDeclNGen_972_ = lean_ctor_get(v___x_967_, 3);
v_cache_973_ = lean_ctor_get(v___x_967_, 5);
v_messages_974_ = lean_ctor_get(v___x_967_, 6);
v_infoState_975_ = lean_ctor_get(v___x_967_, 7);
v_snapshotTasks_976_ = lean_ctor_get(v___x_967_, 8);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_999_ == 0)
{
v___x_978_ = v___x_967_;
v_isShared_979_ = v_isSharedCheck_999_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_snapshotTasks_976_);
lean_inc(v_infoState_975_);
lean_inc(v_messages_974_);
lean_inc(v_cache_973_);
lean_inc(v_traceState_968_);
lean_inc(v_auxDeclNGen_972_);
lean_inc(v_ngen_971_);
lean_inc(v_nextMacroScope_970_);
lean_inc(v_env_969_);
lean_dec(v___x_967_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_999_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
uint64_t v_tid_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_997_; 
v_tid_980_ = lean_ctor_get_uint64(v_traceState_968_, sizeof(void*)*1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_traceState_968_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_traceState_968_, 0);
lean_dec(v_unused_998_);
v___x_982_ = v_traceState_968_;
v_isShared_983_ = v_isSharedCheck_997_;
goto v_resetjp_981_;
}
else
{
lean_dec(v_traceState_968_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_997_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_ref_929_);
lean_ctor_set(v___x_984_, 1, v_a_963_);
v___x_985_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_927_, v___x_984_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 0, v___x_985_);
v___x_987_ = v___x_982_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_985_);
lean_ctor_set_uint64(v_reuseFailAlloc_996_, sizeof(void*)*1, v_tid_980_);
v___x_987_ = v_reuseFailAlloc_996_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_989_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 4, v___x_987_);
v___x_989_ = v___x_978_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_env_969_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_nextMacroScope_970_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v_ngen_971_);
lean_ctor_set(v_reuseFailAlloc_995_, 3, v_auxDeclNGen_972_);
lean_ctor_set(v_reuseFailAlloc_995_, 4, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_995_, 5, v_cache_973_);
lean_ctor_set(v_reuseFailAlloc_995_, 6, v_messages_974_);
lean_ctor_set(v_reuseFailAlloc_995_, 7, v_infoState_975_);
lean_ctor_set(v_reuseFailAlloc_995_, 8, v_snapshotTasks_976_);
v___x_989_ = v_reuseFailAlloc_995_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_990_ = lean_st_ref_set(v___y_934_, v___x_989_);
v___x_991_ = lean_box(0);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_991_);
v___x_993_ = v___x_965_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2___boxed(lean_object* v_oldTraces_1001_, lean_object* v_data_1002_, lean_object* v_ref_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2(v_oldTraces_1001_, v_data_1002_, v_ref_1003_, v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1010_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1011_; double v___x_1012_; 
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_float_of_nat(v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__1));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1016_; double v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(1000u);
v___x_1017_ = lean_float_of_nat(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_cls_1018_, uint8_t v_collapsed_1019_, lean_object* v_tag_1020_, lean_object* v_opts_1021_, uint8_t v_clsEnabled_1022_, lean_object* v_oldTraces_1023_, lean_object* v_msg_1024_, lean_object* v_resStartStop_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___y_1034_; lean_object* v___y_1035_; lean_object* v_data_1036_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; lean_object* v___y_1044_; lean_object* v_a_1045_; uint8_t v___y_1060_; double v___y_1091_; 
v_fst_1031_ = lean_ctor_get(v_resStartStop_1025_, 0);
lean_inc(v_fst_1031_);
v_snd_1032_ = lean_ctor_get(v_resStartStop_1025_, 1);
lean_inc(v_snd_1032_);
lean_dec_ref(v_resStartStop_1025_);
v_fst_1039_ = lean_ctor_get(v_snd_1032_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v_snd_1032_, 1);
lean_inc(v_snd_1040_);
lean_dec(v_snd_1032_);
v___x_1041_ = l_Lean_trace_profiler;
v___x_1042_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_opts_1021_, v___x_1041_);
if (v___x_1042_ == 0)
{
v___y_1060_ = v___x_1042_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1097_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_opts_1021_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; lean_object* v___x_1099_; double v___x_1100_; double v___x_1101_; double v___x_1102_; 
v___x_1098_ = l_Lean_trace_profiler_threshold;
v___x_1099_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(v_opts_1021_, v___x_1098_);
v___x_1100_ = lean_float_of_nat(v___x_1099_);
v___x_1101_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3);
v___x_1102_ = lean_float_div(v___x_1100_, v___x_1101_);
v___y_1091_ = v___x_1102_;
goto v___jp_1090_;
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; double v___x_1105_; 
v___x_1103_ = l_Lean_trace_profiler_threshold;
v___x_1104_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(v_opts_1021_, v___x_1103_);
v___x_1105_ = lean_float_of_nat(v___x_1104_);
v___y_1091_ = v___x_1105_;
goto v___jp_1090_;
}
}
v___jp_1033_:
{
lean_object* v___x_1037_; 
lean_inc(v___y_1034_);
v___x_1037_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2(v_oldTraces_1023_, v_data_1036_, v___y_1034_, v___y_1035_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref_known(v___x_1037_, 1);
v___x_1038_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(v_fst_1031_);
return v___x_1038_;
}
else
{
lean_dec(v_fst_1031_);
return v___x_1037_;
}
}
v___jp_1043_:
{
uint8_t v_result_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; double v___x_1049_; lean_object* v_data_1050_; 
v_result_1046_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__4(v_fst_1031_);
v___x_1047_ = lean_box(v_result_1046_);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
v___x_1049_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0);
lean_inc_ref(v_tag_1020_);
lean_inc_ref(v___x_1048_);
lean_inc(v_cls_1018_);
v_data_1050_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1050_, 0, v_cls_1018_);
lean_ctor_set(v_data_1050_, 1, v___x_1048_);
lean_ctor_set(v_data_1050_, 2, v_tag_1020_);
lean_ctor_set_float(v_data_1050_, sizeof(void*)*3, v___x_1049_);
lean_ctor_set_float(v_data_1050_, sizeof(void*)*3 + 8, v___x_1049_);
lean_ctor_set_uint8(v_data_1050_, sizeof(void*)*3 + 16, v_collapsed_1019_);
if (v___x_1042_ == 0)
{
lean_dec_ref_known(v___x_1048_, 1);
lean_dec(v_snd_1040_);
lean_dec(v_fst_1039_);
lean_dec_ref(v_tag_1020_);
lean_dec(v_cls_1018_);
v___y_1034_ = v___y_1044_;
v___y_1035_ = v_a_1045_;
v_data_1036_ = v_data_1050_;
goto v___jp_1033_;
}
else
{
lean_object* v_data_1051_; double v___x_1052_; double v___x_1053_; 
lean_dec_ref_known(v_data_1050_, 3);
v_data_1051_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1051_, 0, v_cls_1018_);
lean_ctor_set(v_data_1051_, 1, v___x_1048_);
lean_ctor_set(v_data_1051_, 2, v_tag_1020_);
v___x_1052_ = lean_unbox_float(v_fst_1039_);
lean_dec(v_fst_1039_);
lean_ctor_set_float(v_data_1051_, sizeof(void*)*3, v___x_1052_);
v___x_1053_ = lean_unbox_float(v_snd_1040_);
lean_dec(v_snd_1040_);
lean_ctor_set_float(v_data_1051_, sizeof(void*)*3 + 8, v___x_1053_);
lean_ctor_set_uint8(v_data_1051_, sizeof(void*)*3 + 16, v_collapsed_1019_);
v___y_1034_ = v___y_1044_;
v___y_1035_ = v_a_1045_;
v_data_1036_ = v_data_1051_;
goto v___jp_1033_;
}
}
v___jp_1054_:
{
lean_object* v_ref_1055_; lean_object* v___x_1056_; 
v_ref_1055_ = lean_ctor_get(v___y_1028_, 5);
lean_inc(v___y_1029_);
lean_inc_ref(v___y_1028_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v_fst_1031_);
v___x_1056_ = lean_apply_6(v_msg_1024_, v_fst_1031_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, lean_box(0));
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___y_1044_ = v_ref_1055_;
v_a_1045_ = v_a_1057_;
goto v___jp_1043_;
}
else
{
lean_object* v___x_1058_; 
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2);
v___y_1044_ = v_ref_1055_;
v_a_1045_ = v___x_1058_;
goto v___jp_1043_;
}
}
v___jp_1059_:
{
if (v_clsEnabled_1022_ == 0)
{
if (v___y_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v_traceState_1062_; lean_object* v_env_1063_; lean_object* v_nextMacroScope_1064_; lean_object* v_ngen_1065_; lean_object* v_auxDeclNGen_1066_; lean_object* v_cache_1067_; lean_object* v_messages_1068_; lean_object* v_infoState_1069_; lean_object* v_snapshotTasks_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1089_; 
lean_dec(v_snd_1040_);
lean_dec(v_fst_1039_);
lean_dec_ref(v_msg_1024_);
lean_dec_ref(v_tag_1020_);
lean_dec(v_cls_1018_);
v___x_1061_ = lean_st_ref_take(v___y_1029_);
v_traceState_1062_ = lean_ctor_get(v___x_1061_, 4);
v_env_1063_ = lean_ctor_get(v___x_1061_, 0);
v_nextMacroScope_1064_ = lean_ctor_get(v___x_1061_, 1);
v_ngen_1065_ = lean_ctor_get(v___x_1061_, 2);
v_auxDeclNGen_1066_ = lean_ctor_get(v___x_1061_, 3);
v_cache_1067_ = lean_ctor_get(v___x_1061_, 5);
v_messages_1068_ = lean_ctor_get(v___x_1061_, 6);
v_infoState_1069_ = lean_ctor_get(v___x_1061_, 7);
v_snapshotTasks_1070_ = lean_ctor_get(v___x_1061_, 8);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1072_ = v___x_1061_;
v_isShared_1073_ = v_isSharedCheck_1089_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_snapshotTasks_1070_);
lean_inc(v_infoState_1069_);
lean_inc(v_messages_1068_);
lean_inc(v_cache_1067_);
lean_inc(v_traceState_1062_);
lean_inc(v_auxDeclNGen_1066_);
lean_inc(v_ngen_1065_);
lean_inc(v_nextMacroScope_1064_);
lean_inc(v_env_1063_);
lean_dec(v___x_1061_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1089_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
uint64_t v_tid_1074_; lean_object* v_traces_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1088_; 
v_tid_1074_ = lean_ctor_get_uint64(v_traceState_1062_, sizeof(void*)*1);
v_traces_1075_ = lean_ctor_get(v_traceState_1062_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_traceState_1062_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1077_ = v_traceState_1062_;
v_isShared_1078_ = v_isSharedCheck_1088_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_traces_1075_);
lean_dec(v_traceState_1062_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1088_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1023_, v_traces_1075_);
lean_dec_ref(v_traces_1075_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1079_);
lean_ctor_set_uint64(v_reuseFailAlloc_1087_, sizeof(void*)*1, v_tid_1074_);
v___x_1081_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 4, v___x_1081_);
v___x_1083_ = v___x_1072_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_env_1063_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_nextMacroScope_1064_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_ngen_1065_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_auxDeclNGen_1066_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1086_, 5, v_cache_1067_);
lean_ctor_set(v_reuseFailAlloc_1086_, 6, v_messages_1068_);
lean_ctor_set(v_reuseFailAlloc_1086_, 7, v_infoState_1069_);
lean_ctor_set(v_reuseFailAlloc_1086_, 8, v_snapshotTasks_1070_);
v___x_1083_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_st_ref_set(v___y_1029_, v___x_1083_);
v___x_1085_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(v_fst_1031_);
return v___x_1085_;
}
}
}
}
}
else
{
goto v___jp_1054_;
}
}
else
{
goto v___jp_1054_;
}
}
v___jp_1090_:
{
double v___x_1092_; double v___x_1093_; double v___x_1094_; uint8_t v___x_1095_; 
v___x_1092_ = lean_unbox_float(v_snd_1040_);
v___x_1093_ = lean_unbox_float(v_fst_1039_);
v___x_1094_ = lean_float_sub(v___x_1092_, v___x_1093_);
v___x_1095_ = lean_float_decLt(v___y_1091_, v___x_1094_);
v___y_1060_ = v___x_1095_;
goto v___jp_1059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_cls_1106_, lean_object* v_collapsed_1107_, lean_object* v_tag_1108_, lean_object* v_opts_1109_, lean_object* v_clsEnabled_1110_, lean_object* v_oldTraces_1111_, lean_object* v_msg_1112_, lean_object* v_resStartStop_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v_collapsed_boxed_1119_; uint8_t v_clsEnabled_boxed_1120_; lean_object* v_res_1121_; 
v_collapsed_boxed_1119_ = lean_unbox(v_collapsed_1107_);
v_clsEnabled_boxed_1120_ = lean_unbox(v_clsEnabled_1110_);
v_res_1121_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_cls_1106_, v_collapsed_boxed_1119_, v_tag_1108_, v_opts_1109_, v_clsEnabled_boxed_1120_, v_oldTraces_1111_, v_msg_1112_, v_resStartStop_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec_ref(v_opts_1109_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(lean_object* v_cls_1125_, lean_object* v_msg_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_ref_1132_; lean_object* v___x_1133_; lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1178_; 
v_ref_1132_ = lean_ctor_get(v___y_1129_, 5);
v___x_1133_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1178_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1178_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v_traceState_1139_; lean_object* v_env_1140_; lean_object* v_nextMacroScope_1141_; lean_object* v_ngen_1142_; lean_object* v_auxDeclNGen_1143_; lean_object* v_cache_1144_; lean_object* v_messages_1145_; lean_object* v_infoState_1146_; lean_object* v_snapshotTasks_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1177_; 
v___x_1138_ = lean_st_ref_take(v___y_1130_);
v_traceState_1139_ = lean_ctor_get(v___x_1138_, 4);
v_env_1140_ = lean_ctor_get(v___x_1138_, 0);
v_nextMacroScope_1141_ = lean_ctor_get(v___x_1138_, 1);
v_ngen_1142_ = lean_ctor_get(v___x_1138_, 2);
v_auxDeclNGen_1143_ = lean_ctor_get(v___x_1138_, 3);
v_cache_1144_ = lean_ctor_get(v___x_1138_, 5);
v_messages_1145_ = lean_ctor_get(v___x_1138_, 6);
v_infoState_1146_ = lean_ctor_get(v___x_1138_, 7);
v_snapshotTasks_1147_ = lean_ctor_get(v___x_1138_, 8);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1149_ = v___x_1138_;
v_isShared_1150_ = v_isSharedCheck_1177_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_snapshotTasks_1147_);
lean_inc(v_infoState_1146_);
lean_inc(v_messages_1145_);
lean_inc(v_cache_1144_);
lean_inc(v_traceState_1139_);
lean_inc(v_auxDeclNGen_1143_);
lean_inc(v_ngen_1142_);
lean_inc(v_nextMacroScope_1141_);
lean_inc(v_env_1140_);
lean_dec(v___x_1138_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1177_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint64_t v_tid_1151_; lean_object* v_traces_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1176_; 
v_tid_1151_ = lean_ctor_get_uint64(v_traceState_1139_, sizeof(void*)*1);
v_traces_1152_ = lean_ctor_get(v_traceState_1139_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_traceState_1139_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1154_ = v_traceState_1139_;
v_isShared_1155_ = v_isSharedCheck_1176_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_traces_1152_);
lean_dec(v_traceState_1139_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1176_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; double v___x_1157_; uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1156_ = lean_box(0);
v___x_1157_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0);
v___x_1158_ = 0;
v___x_1159_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__0));
v___x_1160_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1160_, 0, v_cls_1125_);
lean_ctor_set(v___x_1160_, 1, v___x_1156_);
lean_ctor_set(v___x_1160_, 2, v___x_1159_);
lean_ctor_set_float(v___x_1160_, sizeof(void*)*3, v___x_1157_);
lean_ctor_set_float(v___x_1160_, sizeof(void*)*3 + 8, v___x_1157_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*3 + 16, v___x_1158_);
v___x_1161_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__1));
v___x_1162_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1160_);
lean_ctor_set(v___x_1162_, 1, v_a_1134_);
lean_ctor_set(v___x_1162_, 2, v___x_1161_);
lean_inc(v_ref_1132_);
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_ref_1132_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
v___x_1164_ = l_Lean_PersistentArray_push___redArg(v_traces_1152_, v___x_1163_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1164_);
v___x_1166_ = v___x_1154_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1164_);
lean_ctor_set_uint64(v_reuseFailAlloc_1175_, sizeof(void*)*1, v_tid_1151_);
v___x_1166_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 4, v___x_1166_);
v___x_1168_ = v___x_1149_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_env_1140_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_nextMacroScope_1141_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_ngen_1142_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_auxDeclNGen_1143_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1174_, 5, v_cache_1144_);
lean_ctor_set(v_reuseFailAlloc_1174_, 6, v_messages_1145_);
lean_ctor_set(v_reuseFailAlloc_1174_, 7, v_infoState_1146_);
lean_ctor_set(v_reuseFailAlloc_1174_, 8, v_snapshotTasks_1147_);
v___x_1168_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = lean_st_ref_set(v___y_1130_, v___x_1168_);
v___x_1170_ = lean_box(0);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1170_);
v___x_1172_ = v___x_1136_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___boxed(lean_object* v_cls_1179_, lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1179_, v_msg_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(lean_object* v_declName_1187_, lean_object* v_as_1188_, size_t v_i_1189_, size_t v_stop_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_usize_dec_eq(v_i_1189_, v_stop_1190_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_array_uget_borrowed(v_as_1188_, v_i_1189_);
lean_inc(v___x_1198_);
lean_inc(v_declName_1187_);
v___x_1199_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1187_, v___x_1198_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; size_t v___x_1201_; size_t v___x_1202_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref_known(v___x_1199_, 1);
v___x_1201_ = ((size_t)1ULL);
v___x_1202_ = lean_usize_add(v_i_1189_, v___x_1201_);
v_i_1189_ = v___x_1202_;
v_b_1191_ = v_a_1200_;
goto _start;
}
else
{
lean_dec(v_declName_1187_);
return v___x_1199_;
}
}
else
{
lean_object* v___x_1204_; 
lean_dec(v_declName_1187_);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v_b_1191_);
return v___x_1204_;
}
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1214_; double v___x_1215_; 
v___x_1214_ = lean_unsigned_to_nat(1000000000u);
v___x_1215_ = lean_float_of_nat(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
lean_object* v_cls_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_cls_1219_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_1220_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7));
v___x_1221_ = l_Lean_Name_append(v___x_1220_, v_cls_1219_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9));
v___x_1224_ = l_Lean_stringToMessageData(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1227_ = l_Lean_stringToMessageData(v___x_1226_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13));
v___x_1230_ = l_Lean_stringToMessageData(v___x_1229_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18(void){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__18);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = lean_box(0);
v___x_1237_ = lean_unsigned_to_nat(16u);
v___x_1238_ = lean_mk_array(v___x_1237_, v___x_1236_);
return v___x_1238_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__16);
v___x_1240_ = lean_unsigned_to_nat(0u);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v___x_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
v___x_1243_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17);
v___x_1244_ = 1;
v___x_1245_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1242_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*2, v___x_1244_);
return v___x_1245_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_unsigned_to_nat(32u);
v___x_1247_ = lean_mk_empty_array_with_capacity(v___x_1246_);
v___x_1248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
return v___x_1248_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
size_t v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1249_ = ((size_t)5ULL);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_unsigned_to_nat(32u);
v___x_1252_ = lean_mk_empty_array_with_capacity(v___x_1251_);
v___x_1253_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22);
v___x_1254_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
lean_ctor_set(v___x_1254_, 1, v___x_1252_);
lean_ctor_set(v___x_1254_, 2, v___x_1250_);
lean_ctor_set(v___x_1254_, 3, v___x_1250_);
lean_ctor_set_usize(v___x_1254_, 4, v___x_1249_);
return v___x_1254_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1256_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
v___x_1257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
lean_ctor_set(v___x_1257_, 3, v___x_1255_);
return v___x_1257_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
lean_ctor_set(v___x_1260_, 1, v___x_1258_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24);
v___x_1262_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
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
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_declName_1272_, v_val_1270_, v___x_1285_, v___x_1286_, v___x_1280_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1287_;
}
}
else
{
size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = lean_usize_of_nat(v___x_1279_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_declName_1272_, v_val_1270_, v___x_1288_, v___x_1289_, v___x_1280_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
return v___x_1290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_1291_, lean_object* v___x_1292_, lean_object* v_declName_1293_, lean_object* v_____r_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1291_, v___x_1292_, v_declName_1293_, v_____r_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___x_1292_);
lean_dec_ref(v_val_1291_);
return v_res_1300_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1318_ = l_Lean_stringToMessageData(v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1319_, lean_object* v_mvarId_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v_options_1363_; lean_object* v_inheritedTraceOptions_1364_; uint8_t v_hasTrace_1365_; lean_object* v_cls_1366_; uint8_t v___x_1367_; 
v_options_1363_ = lean_ctor_get(v_a_1323_, 2);
v_inheritedTraceOptions_1364_ = lean_ctor_get(v_a_1323_, 13);
v_hasTrace_1365_ = lean_ctor_get_uint8(v_options_1363_, sizeof(void*)*1);
v_cls_1366_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_1367_ = lean_bool_not(v_hasTrace_1365_);
if (v___x_1367_ == 0)
{
lean_object* v___f_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___y_1372_; lean_object* v___y_1373_; uint8_t v___y_1374_; lean_object* v_a_1375_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1387_; lean_object* v_a_1388_; lean_object* v___y_1391_; lean_object* v___y_1392_; uint8_t v___y_1393_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; lean_object* v_a_1399_; lean_object* v___y_1402_; lean_object* v___y_1403_; uint8_t v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1412_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; lean_object* v___y_1433_; lean_object* v___y_1434_; uint8_t v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1439_; lean_object* v___y_1440_; uint8_t v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; uint8_t v___y_1448_; lean_object* v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1457_; lean_object* v___y_1458_; uint8_t v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1464_; lean_object* v___y_1465_; uint8_t v___y_1466_; lean_object* v_a_1467_; lean_object* v___y_1480_; lean_object* v___y_1481_; uint8_t v___y_1482_; lean_object* v_a_1483_; lean_object* v___y_1486_; lean_object* v___y_1487_; uint8_t v___y_1488_; lean_object* v___y_1491_; lean_object* v___y_1492_; uint8_t v___y_1493_; lean_object* v_a_1494_; lean_object* v___y_1497_; lean_object* v___y_1498_; uint8_t v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; uint8_t v___y_1507_; lean_object* v___y_1510_; lean_object* v___y_1511_; uint8_t v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1516_; lean_object* v___y_1517_; uint8_t v___y_1518_; lean_object* v___y_1522_; lean_object* v___y_1523_; uint8_t v___y_1524_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; uint8_t v___y_1531_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; uint8_t v___y_1537_; lean_object* v___y_1540_; lean_object* v___y_1541_; uint8_t v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; uint8_t v___y_1549_; lean_object* v___y_1552_; lean_object* v___y_1553_; uint8_t v___y_1554_; lean_object* v___y_1555_; uint8_t v___y_1559_; uint8_t v_a_1829_; 
lean_inc(v_mvarId_1320_);
v___f_1368_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1368_, 0, v_mvarId_1320_);
v___x_1369_ = 1;
v___x_1370_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__0));
if (v_hasTrace_1365_ == 0)
{
v_a_1829_ = v_hasTrace_1365_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2028_);
if (v___x_2029_ == 0)
{
v_a_1829_ = v___x_2029_;
goto v___jp_1828_;
}
else
{
v___y_1559_ = v___x_2029_;
goto v___jp_1558_;
}
}
v___jp_1371_:
{
lean_object* v___x_1376_; double v___x_1377_; double v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1376_ = lean_io_get_num_heartbeats();
v___x_1377_ = lean_float_of_nat(v___y_1372_);
v___x_1378_ = lean_float_of_nat(v___x_1376_);
v___x_1379_ = lean_box_float(v___x_1377_);
v___x_1380_ = lean_box_float(v___x_1378_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_a_1375_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
v___x_1383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_cls_1366_, v___x_1369_, v___x_1370_, v_options_1363_, v___y_1374_, v___y_1373_, v___f_1368_, v___x_1382_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1383_;
}
v___jp_1384_:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v_a_1388_);
v___y_1372_ = v___y_1385_;
v___y_1373_ = v___y_1386_;
v___y_1374_ = v___y_1387_;
v_a_1375_ = v___x_1389_;
goto v___jp_1371_;
}
v___jp_1390_:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_box(0);
v___y_1385_ = v___y_1391_;
v___y_1386_ = v___y_1392_;
v___y_1387_ = v___y_1393_;
v_a_1388_ = v___x_1394_;
goto v___jp_1384_;
}
v___jp_1395_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1399_);
v___y_1372_ = v___y_1396_;
v___y_1373_ = v___y_1397_;
v___y_1374_ = v___y_1398_;
v_a_1375_ = v___x_1400_;
goto v___jp_1371_;
}
v___jp_1401_:
{
if (lean_obj_tag(v___y_1405_) == 0)
{
lean_object* v_a_1406_; 
v_a_1406_ = lean_ctor_get(v___y_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___y_1405_, 1);
v___y_1385_ = v___y_1402_;
v___y_1386_ = v___y_1403_;
v___y_1387_ = v___y_1404_;
v_a_1388_ = v_a_1406_;
goto v___jp_1384_;
}
else
{
lean_object* v_a_1407_; 
v_a_1407_ = lean_ctor_get(v___y_1405_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___y_1405_, 1);
v___y_1396_ = v___y_1402_;
v___y_1397_ = v___y_1403_;
v___y_1398_ = v___y_1404_;
v_a_1399_ = v_a_1407_;
goto v___jp_1395_;
}
}
v___jp_1408_:
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1411_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1409_;
v___y_1403_ = v___y_1410_;
v___y_1404_ = v___y_1412_;
v___y_1405_ = v___x_1413_;
goto v___jp_1401_;
}
v___jp_1414_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v___y_1417_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1415_;
v___y_1403_ = v___y_1416_;
v___y_1404_ = v___y_1418_;
v___y_1405_ = v___x_1419_;
goto v___jp_1401_;
}
v___jp_1420_:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_box(0);
v___x_1425_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1424_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1421_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1423_;
v___y_1405_ = v___x_1425_;
goto v___jp_1401_;
}
v___jp_1426_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1430_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1428_;
v___y_1404_ = v___y_1429_;
v___y_1405_ = v___x_1431_;
goto v___jp_1401_;
}
v___jp_1432_:
{
lean_object* v___x_1437_; 
v___x_1437_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1436_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1433_;
v___y_1403_ = v___y_1434_;
v___y_1404_ = v___y_1435_;
v___y_1405_ = v___x_1437_;
goto v___jp_1401_;
}
v___jp_1438_:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1442_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1439_;
v___y_1403_ = v___y_1440_;
v___y_1404_ = v___y_1441_;
v___y_1405_ = v___x_1443_;
goto v___jp_1401_;
}
v___jp_1444_:
{
lean_object* v___x_1449_; 
v___x_1449_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1447_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1445_;
v___y_1403_ = v___y_1446_;
v___y_1404_ = v___y_1448_;
v___y_1405_ = v___x_1449_;
goto v___jp_1401_;
}
v___jp_1450_:
{
lean_object* v___x_1455_; 
v___x_1455_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1454_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___y_1451_;
v___y_1403_ = v___y_1452_;
v___y_1404_ = v___y_1453_;
v___y_1405_ = v___x_1455_;
goto v___jp_1401_;
}
v___jp_1456_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_box(0);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
v___x_1462_ = lean_apply_6(v___y_1460_, v___x_1461_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, lean_box(0));
v___y_1402_ = v___y_1457_;
v___y_1403_ = v___y_1458_;
v___y_1404_ = v___y_1459_;
v___y_1405_ = v___x_1462_;
goto v___jp_1401_;
}
v___jp_1463_:
{
lean_object* v___x_1468_; double v___x_1469_; double v___x_1470_; double v___x_1471_; double v___x_1472_; double v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1468_ = lean_io_mono_nanos_now();
v___x_1469_ = lean_float_of_nat(v___y_1465_);
v___x_1470_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1471_ = lean_float_div(v___x_1469_, v___x_1470_);
v___x_1472_ = lean_float_of_nat(v___x_1468_);
v___x_1473_ = lean_float_div(v___x_1472_, v___x_1470_);
v___x_1474_ = lean_box_float(v___x_1471_);
v___x_1475_ = lean_box_float(v___x_1473_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1474_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_a_1467_);
lean_ctor_set(v___x_1477_, 1, v___x_1476_);
v___x_1478_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_cls_1366_, v___x_1369_, v___x_1370_, v_options_1363_, v___y_1466_, v___y_1464_, v___f_1368_, v___x_1477_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1478_;
}
v___jp_1479_:
{
lean_object* v___x_1484_; 
v___x_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1484_, 0, v_a_1483_);
v___y_1464_ = v___y_1480_;
v___y_1465_ = v___y_1481_;
v___y_1466_ = v___y_1482_;
v_a_1467_ = v___x_1484_;
goto v___jp_1463_;
}
v___jp_1485_:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_box(0);
v___y_1480_ = v___y_1486_;
v___y_1481_ = v___y_1487_;
v___y_1482_ = v___y_1488_;
v_a_1483_ = v___x_1489_;
goto v___jp_1479_;
}
v___jp_1490_:
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_a_1494_);
v___y_1464_ = v___y_1491_;
v___y_1465_ = v___y_1492_;
v___y_1466_ = v___y_1493_;
v_a_1467_ = v___x_1495_;
goto v___jp_1463_;
}
v___jp_1496_:
{
if (lean_obj_tag(v___y_1500_) == 0)
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___y_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___y_1500_, 1);
v___y_1480_ = v___y_1497_;
v___y_1481_ = v___y_1498_;
v___y_1482_ = v___y_1499_;
v_a_1483_ = v_a_1501_;
goto v___jp_1479_;
}
else
{
lean_object* v_a_1502_; 
v_a_1502_ = lean_ctor_get(v___y_1500_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v___y_1500_, 1);
v___y_1491_ = v___y_1497_;
v___y_1492_ = v___y_1498_;
v___y_1493_ = v___y_1499_;
v_a_1494_ = v_a_1502_;
goto v___jp_1490_;
}
}
v___jp_1503_:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1505_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1504_;
v___y_1498_ = v___y_1506_;
v___y_1499_ = v___y_1507_;
v___y_1500_ = v___x_1508_;
goto v___jp_1496_;
}
v___jp_1509_:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v___y_1513_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1510_;
v___y_1498_ = v___y_1511_;
v___y_1499_ = v___y_1512_;
v___y_1500_ = v___x_1514_;
goto v___jp_1496_;
}
v___jp_1515_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1519_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1516_;
v___y_1498_ = v___y_1517_;
v___y_1499_ = v___y_1518_;
v___y_1500_ = v___x_1520_;
goto v___jp_1496_;
}
v___jp_1521_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1525_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1522_;
v___y_1498_ = v___y_1523_;
v___y_1499_ = v___y_1524_;
v___y_1500_ = v___x_1526_;
goto v___jp_1496_;
}
v___jp_1527_:
{
lean_object* v___x_1532_; 
v___x_1532_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1529_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1528_;
v___y_1498_ = v___y_1530_;
v___y_1499_ = v___y_1531_;
v___y_1500_ = v___x_1532_;
goto v___jp_1496_;
}
v___jp_1533_:
{
lean_object* v___x_1538_; 
v___x_1538_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1535_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1534_;
v___y_1498_ = v___y_1536_;
v___y_1499_ = v___y_1537_;
v___y_1500_ = v___x_1538_;
goto v___jp_1496_;
}
v___jp_1539_:
{
lean_object* v___x_1544_; 
v___x_1544_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1543_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1540_;
v___y_1498_ = v___y_1541_;
v___y_1499_ = v___y_1542_;
v___y_1500_ = v___x_1544_;
goto v___jp_1496_;
}
v___jp_1545_:
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v___y_1548_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v___y_1546_;
v___y_1498_ = v___y_1547_;
v___y_1499_ = v___y_1549_;
v___y_1500_ = v___x_1550_;
goto v___jp_1496_;
}
v___jp_1551_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_box(0);
lean_inc(v_a_1324_);
lean_inc_ref(v_a_1323_);
lean_inc(v_a_1322_);
lean_inc_ref(v_a_1321_);
v___x_1557_ = lean_apply_6(v___y_1555_, v___x_1556_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, lean_box(0));
v___y_1497_ = v___y_1552_;
v___y_1498_ = v___y_1553_;
v___y_1499_ = v___y_1554_;
v___y_1500_ = v___x_1557_;
goto v___jp_1496_;
}
v___jp_1558_:
{
lean_object* v___x_1560_; 
v___x_1560_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_a_1324_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_object* v_a_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1563_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_options_1363_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1320_);
v___x_1565_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; uint8_t v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = lean_unbox(v_a_1566_);
lean_dec(v_a_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_inc(v_mvarId_1320_);
v___x_1568_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; uint8_t v___x_1570_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v___x_1570_ = lean_unbox(v_a_1569_);
lean_dec(v_a_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; 
lean_inc(v_mvarId_1320_);
v___x_1571_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
if (lean_obj_tag(v_a_1572_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1573_; 
v_val_1573_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v_a_1572_, 1);
v___y_1528_ = v_a_1561_;
v___y_1529_ = v_val_1573_;
v___y_1530_ = v___x_1564_;
v___y_1531_ = v___y_1559_;
goto v___jp_1527_;
}
else
{
lean_object* v_val_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_val_1574_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v_a_1572_, 1);
v___x_1575_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1576_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1575_);
if (v___x_1576_ == 0)
{
v___y_1528_ = v_a_1561_;
v___y_1529_ = v_val_1574_;
v___y_1530_ = v___x_1564_;
v___y_1531_ = v___y_1559_;
goto v___jp_1527_;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1578_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1577_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_dec_ref_known(v___x_1578_, 1);
v___x_1579_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1574_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1579_;
goto v___jp_1496_;
}
else
{
lean_dec(v_val_1574_);
lean_dec(v_declName_1319_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1578_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_object* v___x_1580_; 
lean_dec(v_a_1572_);
lean_inc(v_mvarId_1320_);
v___x_1580_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v___x_1580_, 1);
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1582_; 
v_val_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref_known(v_a_1581_, 1);
v___y_1534_ = v_a_1561_;
v___y_1535_ = v_val_1582_;
v___y_1536_ = v___x_1564_;
v___y_1537_ = v___y_1559_;
goto v___jp_1533_;
}
else
{
lean_object* v_val_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_val_1583_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v_a_1581_, 1);
v___x_1584_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1585_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1584_);
if (v___x_1585_ == 0)
{
v___y_1534_ = v_a_1561_;
v___y_1535_ = v_val_1583_;
v___y_1536_ = v___x_1564_;
v___y_1537_ = v___y_1559_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1587_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1586_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v___x_1588_; 
lean_dec_ref_known(v___x_1587_, 1);
v___x_1588_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1583_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1588_;
goto v___jp_1496_;
}
else
{
lean_dec(v_val_1583_);
lean_dec(v_declName_1319_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1587_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_object* v___x_1589_; 
lean_dec(v_a_1581_);
lean_inc(v_mvarId_1320_);
v___x_1589_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1320_, v___x_1369_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v___x_1589_, 1);
if (lean_obj_tag(v_a_1590_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1591_; 
v_val_1591_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v_a_1590_, 1);
v___y_1540_ = v_a_1561_;
v___y_1541_ = v___x_1564_;
v___y_1542_ = v___y_1559_;
v___y_1543_ = v_val_1591_;
goto v___jp_1539_;
}
else
{
lean_object* v_val_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_val_1592_ = lean_ctor_get(v_a_1590_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_a_1590_, 1);
v___x_1593_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1593_);
if (v___x_1594_ == 0)
{
v___y_1540_ = v_a_1561_;
v___y_1541_ = v___x_1564_;
v___y_1542_ = v___y_1559_;
v___y_1543_ = v_val_1592_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14);
v___x_1596_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1595_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v___x_1597_; 
lean_dec_ref_known(v___x_1596_, 1);
v___x_1597_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1592_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1597_;
goto v___jp_1496_;
}
else
{
lean_dec(v_val_1592_);
lean_dec(v_declName_1319_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1596_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
lean_dec(v_a_1590_);
v___x_1598_ = lean_unsigned_to_nat(100000u);
v___x_1599_ = lean_unsigned_to_nat(2u);
v___x_1600_ = 0;
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1602_, 0, v___x_1598_);
lean_ctor_set(v___x_1602_, 1, v___x_1599_);
lean_ctor_set(v___x_1602_, 2, v___x_1601_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 1, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 2, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 3, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 4, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 5, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 6, v___x_1600_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 7, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 8, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 9, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 10, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 11, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 12, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 13, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 14, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 15, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 16, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 17, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 18, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 19, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 20, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 21, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 22, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 23, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 24, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 25, v___x_1369_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 26, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 27, v___x_1563_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*3 + 28, v___x_1563_);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15));
v___x_1605_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1606_ = l_Lean_Options_empty;
v___x_1607_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1602_, v___x_1604_, v___x_1605_, v___x_1606_, v_a_1321_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1608_);
lean_dec_ref_known(v___x_1607_, 1);
v___x_1609_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
lean_inc(v_mvarId_1320_);
v___x_1610_ = l_Lean_Meta_simpTargetStar(v_mvarId_1320_, v_a_1608_, v___x_1604_, v___x_1601_, v___x_1609_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; lean_object* v_fst_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1670_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1610_, 1);
v_fst_1612_ = lean_ctor_get(v_a_1611_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_a_1611_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v_a_1611_, 1);
lean_dec(v_unused_1671_);
v___x_1614_ = v_a_1611_;
v_isShared_1615_ = v_isSharedCheck_1670_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_fst_1612_);
lean_dec(v_a_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1670_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
switch(lean_obj_tag(v_fst_1612_))
{
case 0:
{
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
v___y_1486_ = v_a_1561_;
v___y_1487_ = v___x_1564_;
v___y_1488_ = v___y_1559_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1617_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1616_);
if (v___x_1617_ == 0)
{
v___y_1486_ = v_a_1561_;
v___y_1487_ = v___x_1564_;
v___y_1488_ = v___y_1559_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1619_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1618_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1619_;
goto v___jp_1496_;
}
}
}
case 1:
{
lean_object* v___x_1620_; 
lean_inc(v_declName_1319_);
lean_inc(v_mvarId_1320_);
v___x_1620_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1320_, v_declName_1319_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
if (lean_obj_tag(v_a_1621_) == 1)
{
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1622_; 
v_val_1622_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref_known(v_a_1621_, 1);
v___y_1546_ = v_a_1561_;
v___y_1547_ = v___x_1564_;
v___y_1548_ = v_val_1622_;
v___y_1549_ = v___y_1559_;
goto v___jp_1545_;
}
else
{
lean_object* v_val_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_val_1623_ = lean_ctor_get(v_a_1621_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_a_1621_, 1);
v___x_1624_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1625_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1624_);
if (v___x_1625_ == 0)
{
v___y_1546_ = v_a_1561_;
v___y_1547_ = v___x_1564_;
v___y_1548_ = v_val_1623_;
v___y_1549_ = v___y_1559_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1627_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1626_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v___x_1628_; 
lean_dec_ref_known(v___x_1627_, 1);
v___x_1628_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1623_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1628_;
goto v___jp_1496_;
}
else
{
lean_dec(v_val_1623_);
lean_dec(v_declName_1319_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1627_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_object* v___x_1629_; 
lean_dec(v_a_1621_);
lean_inc(v_mvarId_1320_);
v___x_1629_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
if (lean_obj_tag(v_a_1630_) == 1)
{
lean_object* v_val_1631_; lean_object* v___f_1632_; 
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
v_val_1631_ = lean_ctor_get(v_a_1630_, 0);
lean_inc_n(v_val_1631_, 2);
lean_dec_ref_known(v_a_1630_, 1);
lean_inc(v_declName_1319_);
v___f_1632_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed), 9, 3);
lean_closure_set(v___f_1632_, 0, v_val_1631_);
lean_closure_set(v___f_1632_, 1, v___x_1603_);
lean_closure_set(v___f_1632_, 2, v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
lean_dec(v_val_1631_);
lean_dec(v_declName_1319_);
v___y_1552_ = v_a_1561_;
v___y_1553_ = v___x_1564_;
v___y_1554_ = v___y_1559_;
v___y_1555_ = v___f_1632_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1633_);
if (v___x_1634_ == 0)
{
lean_dec(v_val_1631_);
lean_dec(v_declName_1319_);
v___y_1552_ = v_a_1561_;
v___y_1553_ = v___x_1564_;
v___y_1554_ = v___y_1559_;
v___y_1555_ = v___f_1632_;
goto v___jp_1551_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v___f_1632_);
v___x_1635_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1636_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1635_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1638_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1631_, v___x_1603_, v_declName_1319_, v_a_1637_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_val_1631_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1638_;
goto v___jp_1496_;
}
else
{
lean_dec(v_val_1631_);
lean_dec(v_declName_1319_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1636_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_object* v___x_1639_; 
lean_dec(v_a_1630_);
lean_inc(v_mvarId_1320_);
v___x_1639_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1320_, v___x_1369_, v___x_1369_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1659_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1659_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1659_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
if (lean_obj_tag(v_a_1640_) == 1)
{
lean_del_object(v___x_1642_);
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1644_; 
v_val_1644_ = lean_ctor_get(v_a_1640_, 0);
lean_inc(v_val_1644_);
lean_dec_ref_known(v_a_1640_, 1);
v___y_1510_ = v_a_1561_;
v___y_1511_ = v___x_1564_;
v___y_1512_ = v___y_1559_;
v___y_1513_ = v_val_1644_;
goto v___jp_1509_;
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_val_1645_ = lean_ctor_get(v_a_1640_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v_a_1640_, 1);
v___x_1646_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1647_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1646_);
if (v___x_1647_ == 0)
{
v___y_1510_ = v_a_1561_;
v___y_1511_ = v___x_1564_;
v___y_1512_ = v___y_1559_;
v___y_1513_ = v_val_1645_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1649_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1648_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref_known(v___x_1649_, 1);
v___x_1650_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_1645_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1650_;
goto v___jp_1496_;
}
else
{
lean_dec(v_val_1645_);
lean_dec(v_declName_1319_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1649_;
goto v___jp_1496_;
}
}
}
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_dec(v_a_1640_);
lean_dec(v_declName_1319_);
v___x_1651_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
lean_ctor_set(v___x_1642_, 0, v_mvarId_1320_);
v___x_1653_ = v___x_1642_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_mvarId_1320_);
v___x_1653_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 7);
lean_ctor_set(v___x_1614_, 1, v___x_1653_);
lean_ctor_set(v___x_1614_, 0, v___x_1651_);
v___x_1655_ = v___x_1614_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1655_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1656_;
goto v___jp_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1660_; 
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1660_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1660_);
lean_dec_ref_known(v___x_1639_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1660_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1661_; 
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1661_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1661_);
lean_dec_ref_known(v___x_1629_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1661_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1662_; 
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1662_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1620_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1662_;
goto v___jp_1490_;
}
}
default: 
{
lean_del_object(v___x_1614_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_mvarId_1663_; 
v_mvarId_1663_ = lean_ctor_get(v_fst_1612_, 0);
lean_inc(v_mvarId_1663_);
lean_dec_ref_known(v_fst_1612_, 1);
v___y_1504_ = v_a_1561_;
v___y_1505_ = v_mvarId_1663_;
v___y_1506_ = v___x_1564_;
v___y_1507_ = v___y_1559_;
goto v___jp_1503_;
}
else
{
lean_object* v_mvarId_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_mvarId_1664_ = lean_ctor_get(v_fst_1612_, 0);
lean_inc(v_mvarId_1664_);
lean_dec_ref_known(v_fst_1612_, 1);
v___x_1665_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1665_);
if (v___x_1666_ == 0)
{
v___y_1504_ = v_a_1561_;
v___y_1505_ = v_mvarId_1664_;
v___y_1506_ = v___x_1564_;
v___y_1507_ = v___y_1559_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1668_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1667_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v___x_1669_; 
lean_dec_ref_known(v___x_1668_, 1);
v___x_1669_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_mvarId_1664_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1669_;
goto v___jp_1496_;
}
else
{
lean_dec(v_mvarId_1664_);
lean_dec(v_declName_1319_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1668_;
goto v___jp_1496_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1672_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1672_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v___x_1610_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1672_;
goto v___jp_1490_;
}
}
else
{
lean_object* v_a_1673_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1673_ = lean_ctor_get(v___x_1607_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1607_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1673_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1674_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1674_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1589_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1674_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1675_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1675_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1675_);
lean_dec_ref_known(v___x_1580_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1675_;
goto v___jp_1490_;
}
}
}
else
{
lean_object* v_a_1676_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1676_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1571_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1676_;
goto v___jp_1490_;
}
}
else
{
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
v___y_1516_ = v_a_1561_;
v___y_1517_ = v___x_1564_;
v___y_1518_ = v___y_1559_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1677_);
if (v___x_1678_ == 0)
{
v___y_1516_ = v_a_1561_;
v___y_1517_ = v___x_1564_;
v___y_1518_ = v___y_1559_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1680_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1679_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1682_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref_known(v___x_1680_, 1);
v___x_1682_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1681_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1682_;
goto v___jp_1496_;
}
else
{
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1680_;
goto v___jp_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1683_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1683_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1568_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1683_;
goto v___jp_1490_;
}
}
else
{
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
v___y_1522_ = v_a_1561_;
v___y_1523_ = v___x_1564_;
v___y_1524_ = v___y_1559_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1685_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1684_);
if (v___x_1685_ == 0)
{
v___y_1522_ = v_a_1561_;
v___y_1523_ = v___x_1564_;
v___y_1524_ = v___y_1559_;
goto v___jp_1521_;
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1687_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1686_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
v___x_1689_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1688_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1689_;
goto v___jp_1496_;
}
else
{
v___y_1497_ = v_a_1561_;
v___y_1498_ = v___x_1564_;
v___y_1499_ = v___y_1559_;
v___y_1500_ = v___x_1687_;
goto v___jp_1496_;
}
}
}
}
}
else
{
lean_object* v_a_1690_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1690_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1690_);
lean_dec_ref_known(v___x_1565_, 1);
v___y_1491_ = v_a_1561_;
v___y_1492_ = v___x_1564_;
v___y_1493_ = v___y_1559_;
v_a_1494_ = v_a_1690_;
goto v___jp_1490_;
}
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1320_);
v___x_1692_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; uint8_t v___x_1694_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_unbox(v_a_1693_);
lean_dec(v_a_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; 
lean_inc(v_mvarId_1320_);
v___x_1695_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; uint8_t v___x_1697_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1697_ = lean_unbox(v_a_1696_);
lean_dec(v_a_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
lean_inc(v_mvarId_1320_);
v___x_1698_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
if (lean_obj_tag(v_a_1699_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1700_; 
v_val_1700_ = lean_ctor_get(v_a_1699_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v_a_1699_, 1);
v___y_1433_ = v___x_1691_;
v___y_1434_ = v_a_1561_;
v___y_1435_ = v___y_1559_;
v___y_1436_ = v_val_1700_;
goto v___jp_1432_;
}
else
{
lean_object* v_val_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_val_1701_ = lean_ctor_get(v_a_1699_, 0);
lean_inc(v_val_1701_);
lean_dec_ref_known(v_a_1699_, 1);
v___x_1702_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1703_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1702_);
if (v___x_1703_ == 0)
{
v___y_1433_ = v___x_1691_;
v___y_1434_ = v_a_1561_;
v___y_1435_ = v___y_1559_;
v___y_1436_ = v_val_1701_;
goto v___jp_1432_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1705_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1704_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; 
lean_dec_ref_known(v___x_1705_, 1);
v___x_1706_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1701_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1706_;
goto v___jp_1401_;
}
else
{
lean_dec(v_val_1701_);
lean_dec(v_declName_1319_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1705_;
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v___x_1707_; 
lean_dec(v_a_1699_);
lean_inc(v_mvarId_1320_);
v___x_1707_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref_known(v___x_1707_, 1);
if (lean_obj_tag(v_a_1708_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1709_; 
v_val_1709_ = lean_ctor_get(v_a_1708_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1708_, 1);
v___y_1439_ = v___x_1691_;
v___y_1440_ = v_a_1561_;
v___y_1441_ = v___y_1559_;
v___y_1442_ = v_val_1709_;
goto v___jp_1438_;
}
else
{
lean_object* v_val_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_val_1710_ = lean_ctor_get(v_a_1708_, 0);
lean_inc(v_val_1710_);
lean_dec_ref_known(v_a_1708_, 1);
v___x_1711_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1711_);
if (v___x_1712_ == 0)
{
v___y_1439_ = v___x_1691_;
v___y_1440_ = v_a_1561_;
v___y_1441_ = v___y_1559_;
v___y_1442_ = v_val_1710_;
goto v___jp_1438_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1714_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1713_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v___x_1715_; 
lean_dec_ref_known(v___x_1714_, 1);
v___x_1715_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1710_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1715_;
goto v___jp_1401_;
}
else
{
lean_dec(v_val_1710_);
lean_dec(v_declName_1319_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1714_;
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v___x_1716_; 
lean_dec(v_a_1708_);
lean_inc(v_mvarId_1320_);
v___x_1716_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1320_, v___x_1563_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
if (lean_obj_tag(v_a_1717_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1718_; 
v_val_1718_ = lean_ctor_get(v_a_1717_, 0);
lean_inc(v_val_1718_);
lean_dec_ref_known(v_a_1717_, 1);
v___y_1445_ = v___x_1691_;
v___y_1446_ = v_a_1561_;
v___y_1447_ = v_val_1718_;
v___y_1448_ = v___y_1559_;
goto v___jp_1444_;
}
else
{
lean_object* v_val_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_val_1719_ = lean_ctor_get(v_a_1717_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v_a_1717_, 1);
v___x_1720_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1720_);
if (v___x_1721_ == 0)
{
v___y_1445_ = v___x_1691_;
v___y_1446_ = v_a_1561_;
v___y_1447_ = v_val_1719_;
v___y_1448_ = v___y_1559_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14);
v___x_1723_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1722_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v___x_1724_; 
lean_dec_ref_known(v___x_1723_, 1);
v___x_1724_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1719_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1724_;
goto v___jp_1401_;
}
else
{
lean_dec(v_val_1719_);
lean_dec(v_declName_1319_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1723_;
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec(v_a_1717_);
v___x_1725_ = lean_unsigned_to_nat(100000u);
v___x_1726_ = lean_unsigned_to_nat(2u);
v___x_1727_ = 0;
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1729_, 0, v___x_1725_);
lean_ctor_set(v___x_1729_, 1, v___x_1726_);
lean_ctor_set(v___x_1729_, 2, v___x_1728_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 1, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 2, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 3, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 4, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 5, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 6, v___x_1727_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 7, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 8, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 9, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 10, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 11, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 12, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 13, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 14, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 15, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 16, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 17, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 18, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 19, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 20, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 21, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 22, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 23, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 24, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 25, v___x_1563_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 26, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 27, v___x_1367_);
lean_ctor_set_uint8(v___x_1729_, sizeof(void*)*3 + 28, v___x_1367_);
v___x_1730_ = lean_unsigned_to_nat(0u);
v___x_1731_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15));
v___x_1732_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17);
v___x_1733_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
v___x_1734_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*2, v___x_1563_);
v___x_1735_ = l_Lean_Options_empty;
v___x_1736_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1729_, v___x_1731_, v___x_1734_, v___x_1735_, v_a_1321_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v___x_1738_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
lean_inc(v_mvarId_1320_);
v___x_1739_ = l_Lean_Meta_simpTargetStar(v_mvarId_1320_, v_a_1737_, v___x_1731_, v___x_1728_, v___x_1738_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; lean_object* v_fst_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1799_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v_fst_1741_ = lean_ctor_get(v_a_1740_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_a_1740_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; 
v_unused_1800_ = lean_ctor_get(v_a_1740_, 1);
lean_dec(v_unused_1800_);
v___x_1743_ = v_a_1740_;
v_isShared_1744_ = v_isSharedCheck_1799_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_fst_1741_);
lean_dec(v_a_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1799_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
switch(lean_obj_tag(v_fst_1741_))
{
case 0:
{
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
v___y_1391_ = v___x_1691_;
v___y_1392_ = v_a_1561_;
v___y_1393_ = v___y_1559_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1746_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1745_);
if (v___x_1746_ == 0)
{
v___y_1391_ = v___x_1691_;
v___y_1392_ = v_a_1561_;
v___y_1393_ = v___y_1559_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1748_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1747_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1748_;
goto v___jp_1401_;
}
}
}
case 1:
{
lean_object* v___x_1749_; 
lean_inc(v_declName_1319_);
lean_inc(v_mvarId_1320_);
v___x_1749_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1320_, v_declName_1319_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
if (lean_obj_tag(v_a_1750_) == 1)
{
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1751_; 
v_val_1751_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_val_1751_);
lean_dec_ref_known(v_a_1750_, 1);
v___y_1451_ = v___x_1691_;
v___y_1452_ = v_a_1561_;
v___y_1453_ = v___y_1559_;
v___y_1454_ = v_val_1751_;
goto v___jp_1450_;
}
else
{
lean_object* v_val_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_val_1752_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_val_1752_);
lean_dec_ref_known(v_a_1750_, 1);
v___x_1753_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1753_);
if (v___x_1754_ == 0)
{
v___y_1451_ = v___x_1691_;
v___y_1452_ = v_a_1561_;
v___y_1453_ = v___y_1559_;
v___y_1454_ = v_val_1752_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1756_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1755_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref_known(v___x_1756_, 1);
v___x_1757_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_val_1752_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1757_;
goto v___jp_1401_;
}
else
{
lean_dec(v_val_1752_);
lean_dec(v_declName_1319_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1756_;
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v___x_1758_; 
lean_dec(v_a_1750_);
lean_inc(v_mvarId_1320_);
v___x_1758_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
if (lean_obj_tag(v_a_1759_) == 1)
{
lean_object* v_val_1760_; lean_object* v___f_1761_; 
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
v_val_1760_ = lean_ctor_get(v_a_1759_, 0);
lean_inc_n(v_val_1760_, 2);
lean_dec_ref_known(v_a_1759_, 1);
lean_inc(v_declName_1319_);
v___f_1761_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed), 9, 3);
lean_closure_set(v___f_1761_, 0, v_val_1760_);
lean_closure_set(v___f_1761_, 1, v___x_1730_);
lean_closure_set(v___f_1761_, 2, v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
lean_dec(v_val_1760_);
lean_dec(v_declName_1319_);
v___y_1457_ = v___x_1691_;
v___y_1458_ = v_a_1561_;
v___y_1459_ = v___y_1559_;
v___y_1460_ = v___f_1761_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_dec(v_val_1760_);
lean_dec(v_declName_1319_);
v___y_1457_ = v___x_1691_;
v___y_1458_ = v_a_1561_;
v___y_1459_ = v___y_1559_;
v___y_1460_ = v___f_1761_;
goto v___jp_1456_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec_ref(v___f_1761_);
v___x_1764_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1765_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1764_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v___x_1767_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1760_, v___x_1730_, v_declName_1319_, v_a_1766_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_val_1760_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1767_;
goto v___jp_1401_;
}
else
{
lean_dec(v_val_1760_);
lean_dec(v_declName_1319_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1765_;
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v___x_1768_; 
lean_dec(v_a_1759_);
lean_inc(v_mvarId_1320_);
v___x_1768_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1320_, v___x_1563_, v___x_1563_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1788_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1788_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
if (lean_obj_tag(v_a_1769_) == 1)
{
lean_del_object(v___x_1771_);
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1773_; 
v_val_1773_ = lean_ctor_get(v_a_1769_, 0);
lean_inc(v_val_1773_);
lean_dec_ref_known(v_a_1769_, 1);
v___y_1415_ = v___x_1691_;
v___y_1416_ = v_a_1561_;
v___y_1417_ = v_val_1773_;
v___y_1418_ = v___y_1559_;
goto v___jp_1414_;
}
else
{
lean_object* v_val_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_val_1774_ = lean_ctor_get(v_a_1769_, 0);
lean_inc(v_val_1774_);
lean_dec_ref_known(v_a_1769_, 1);
v___x_1775_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1776_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1775_);
if (v___x_1776_ == 0)
{
v___y_1415_ = v___x_1691_;
v___y_1416_ = v_a_1561_;
v___y_1417_ = v_val_1774_;
v___y_1418_ = v___y_1559_;
goto v___jp_1414_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1778_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1777_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v___x_1779_; 
lean_dec_ref_known(v___x_1778_, 1);
v___x_1779_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_1774_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1779_;
goto v___jp_1401_;
}
else
{
lean_dec(v_val_1774_);
lean_dec(v_declName_1319_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1778_;
goto v___jp_1401_;
}
}
}
}
else
{
lean_object* v___x_1780_; lean_object* v___x_1782_; 
lean_dec(v_a_1769_);
lean_dec(v_declName_1319_);
v___x_1780_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 1);
lean_ctor_set(v___x_1771_, 0, v_mvarId_1320_);
v___x_1782_ = v___x_1771_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_mvarId_1320_);
v___x_1782_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set_tag(v___x_1743_, 7);
lean_ctor_set(v___x_1743_, 1, v___x_1782_);
lean_ctor_set(v___x_1743_, 0, v___x_1780_);
v___x_1784_ = v___x_1743_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1784_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1785_;
goto v___jp_1401_;
}
}
}
}
}
else
{
lean_object* v_a_1789_; 
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1789_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1768_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1789_;
goto v___jp_1395_;
}
}
}
else
{
lean_object* v_a_1790_; 
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1790_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1790_);
lean_dec_ref_known(v___x_1758_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1790_;
goto v___jp_1395_;
}
}
}
else
{
lean_object* v_a_1791_; 
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1791_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1791_);
lean_dec_ref_known(v___x_1749_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1791_;
goto v___jp_1395_;
}
}
default: 
{
lean_del_object(v___x_1743_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_mvarId_1792_; 
v_mvarId_1792_ = lean_ctor_get(v_fst_1741_, 0);
lean_inc(v_mvarId_1792_);
lean_dec_ref_known(v_fst_1741_, 1);
v___y_1409_ = v___x_1691_;
v___y_1410_ = v_a_1561_;
v___y_1411_ = v_mvarId_1792_;
v___y_1412_ = v___y_1559_;
goto v___jp_1408_;
}
else
{
lean_object* v_mvarId_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_mvarId_1793_ = lean_ctor_get(v_fst_1741_, 0);
lean_inc(v_mvarId_1793_);
lean_dec_ref_known(v_fst_1741_, 1);
v___x_1794_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1795_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1794_);
if (v___x_1795_ == 0)
{
v___y_1409_ = v___x_1691_;
v___y_1410_ = v_a_1561_;
v___y_1411_ = v_mvarId_1793_;
v___y_1412_ = v___y_1559_;
goto v___jp_1408_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1797_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1796_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v___x_1798_; 
lean_dec_ref_known(v___x_1797_, 1);
v___x_1798_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1319_, v_mvarId_1793_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1798_;
goto v___jp_1401_;
}
else
{
lean_dec(v_mvarId_1793_);
lean_dec(v_declName_1319_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1797_;
goto v___jp_1401_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1801_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1801_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1739_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1801_;
goto v___jp_1395_;
}
}
else
{
lean_object* v_a_1802_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1802_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1802_);
lean_dec_ref_known(v___x_1736_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1802_;
goto v___jp_1395_;
}
}
}
else
{
lean_object* v_a_1803_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1803_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1803_);
lean_dec_ref_known(v___x_1716_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1803_;
goto v___jp_1395_;
}
}
}
else
{
lean_object* v_a_1804_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1804_ = lean_ctor_get(v___x_1707_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1707_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1804_;
goto v___jp_1395_;
}
}
}
else
{
lean_object* v_a_1805_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1805_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1698_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1805_;
goto v___jp_1395_;
}
}
else
{
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
v___y_1421_ = v___x_1691_;
v___y_1422_ = v_a_1561_;
v___y_1423_ = v___y_1559_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1807_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1806_);
if (v___x_1807_ == 0)
{
v___y_1421_ = v___x_1691_;
v___y_1422_ = v_a_1561_;
v___y_1423_ = v___y_1559_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1809_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1808_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1810_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1811_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1809_;
goto v___jp_1401_;
}
}
}
}
}
else
{
lean_object* v_a_1812_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1812_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1695_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1812_;
goto v___jp_1395_;
}
}
else
{
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
v___y_1427_ = v___x_1691_;
v___y_1428_ = v_a_1561_;
v___y_1429_ = v___y_1559_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1814_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1813_);
if (v___x_1814_ == 0)
{
v___y_1427_ = v___x_1691_;
v___y_1428_ = v_a_1561_;
v___y_1429_ = v___y_1559_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1816_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1815_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1816_) == 0)
{
lean_object* v_a_1817_; lean_object* v___x_1818_; 
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
lean_inc(v_a_1817_);
lean_dec_ref_known(v___x_1816_, 1);
v___x_1818_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1817_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1818_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___x_1691_;
v___y_1403_ = v_a_1561_;
v___y_1404_ = v___y_1559_;
v___y_1405_ = v___x_1816_;
goto v___jp_1401_;
}
}
}
}
}
else
{
lean_object* v_a_1819_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1819_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1819_);
lean_dec_ref_known(v___x_1692_, 1);
v___y_1396_ = v___x_1691_;
v___y_1397_ = v_a_1561_;
v___y_1398_ = v___y_1559_;
v_a_1399_ = v_a_1819_;
goto v___jp_1395_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec_ref(v___f_1368_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1820_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1560_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1560_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
v___jp_1828_:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1830_ = l_Lean_trace_profiler;
v___x_1831_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_options_1363_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec_ref(v___f_1368_);
lean_inc(v_mvarId_1320_);
v___x_1832_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1832_) == 0)
{
lean_object* v_a_1833_; uint8_t v___x_1834_; 
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1832_, 1);
v___x_1834_ = lean_unbox(v_a_1833_);
lean_dec(v_a_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_inc(v_mvarId_1320_);
v___x_1835_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; uint8_t v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref_known(v___x_1835_, 1);
v___x_1837_ = lean_unbox(v_a_1836_);
lean_dec(v_a_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_inc(v_mvarId_1320_);
v___x_1838_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v_a_1839_; 
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
lean_inc(v_a_1839_);
lean_dec_ref_known(v___x_1838_, 1);
if (lean_obj_tag(v_a_1839_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1840_; 
v_val_1840_ = lean_ctor_get(v_a_1839_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v_a_1839_, 1);
v_mvarId_1320_ = v_val_1840_;
goto _start;
}
else
{
lean_object* v_val_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_val_1842_ = lean_ctor_get(v_a_1839_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v_a_1839_, 1);
v___x_1843_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1844_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1843_);
if (v___x_1844_ == 0)
{
v_mvarId_1320_ = v_val_1842_;
goto _start;
}
else
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_1847_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1846_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_dec_ref_known(v___x_1847_, 1);
v_mvarId_1320_ = v_val_1842_;
goto _start;
}
else
{
lean_dec(v_val_1842_);
lean_dec(v_declName_1319_);
return v___x_1847_;
}
}
}
}
else
{
lean_object* v___x_1849_; 
lean_dec(v_a_1839_);
lean_inc(v_mvarId_1320_);
v___x_1849_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
if (lean_obj_tag(v_a_1850_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1851_; 
v_val_1851_ = lean_ctor_get(v_a_1850_, 0);
lean_inc(v_val_1851_);
lean_dec_ref_known(v_a_1850_, 1);
v_mvarId_1320_ = v_val_1851_;
goto _start;
}
else
{
lean_object* v_val_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_val_1853_ = lean_ctor_get(v_a_1850_, 0);
lean_inc(v_val_1853_);
lean_dec_ref_known(v_a_1850_, 1);
v___x_1854_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1854_);
if (v___x_1855_ == 0)
{
v_mvarId_1320_ = v_val_1853_;
goto _start;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1858_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1857_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_dec_ref_known(v___x_1858_, 1);
v_mvarId_1320_ = v_val_1853_;
goto _start;
}
else
{
lean_dec(v_val_1853_);
lean_dec(v_declName_1319_);
return v___x_1858_;
}
}
}
}
else
{
lean_object* v___x_1860_; 
lean_dec(v_a_1850_);
lean_inc(v_mvarId_1320_);
v___x_1860_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1320_, v___x_1369_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_a_1861_);
lean_dec_ref_known(v___x_1860_, 1);
if (lean_obj_tag(v_a_1861_) == 1)
{
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1862_; 
v_val_1862_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_a_1861_, 1);
v_mvarId_1320_ = v_val_1862_;
goto _start;
}
else
{
lean_object* v_val_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_val_1864_ = lean_ctor_get(v_a_1861_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v_a_1861_, 1);
v___x_1865_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1866_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1865_);
if (v___x_1866_ == 0)
{
v_mvarId_1320_ = v_val_1864_;
goto _start;
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14);
v___x_1869_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1868_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec_ref_known(v___x_1869_, 1);
v_mvarId_1320_ = v_val_1864_;
goto _start;
}
else
{
lean_dec(v_val_1864_);
lean_dec(v_declName_1319_);
return v___x_1869_;
}
}
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec(v_a_1861_);
v___x_1871_ = lean_unsigned_to_nat(100000u);
v___x_1872_ = lean_unsigned_to_nat(2u);
v___x_1873_ = 0;
v___x_1874_ = lean_box(0);
v___x_1875_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1875_, 0, v___x_1871_);
lean_ctor_set(v___x_1875_, 1, v___x_1872_);
lean_ctor_set(v___x_1875_, 2, v___x_1874_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 1, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 2, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 3, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 4, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 5, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 6, v___x_1873_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 7, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 8, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 9, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 10, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 11, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 12, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 13, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 14, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 15, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 16, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 17, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 18, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 19, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 20, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 21, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 22, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 23, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 24, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 25, v___x_1369_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 26, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 27, v___x_1831_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*3 + 28, v___x_1831_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15));
v___x_1878_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1879_ = l_Lean_Options_empty;
v___x_1880_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1875_, v___x_1877_, v___x_1878_, v___x_1879_, v_a_1321_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
lean_inc(v_mvarId_1320_);
v___x_1883_ = l_Lean_Meta_simpTargetStar(v_mvarId_1320_, v_a_1881_, v___x_1877_, v___x_1874_, v___x_1882_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v_fst_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1962_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_fst_1885_ = lean_ctor_get(v_a_1884_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v_a_1884_, 1);
lean_dec(v_unused_1963_);
v___x_1887_ = v_a_1884_;
v_isShared_1888_ = v_isSharedCheck_1962_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_fst_1885_);
lean_dec(v_a_1884_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1962_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
switch(lean_obj_tag(v_fst_1885_))
{
case 0:
{
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
goto v___jp_1348_;
}
else
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1890_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1889_);
if (v___x_1890_ == 0)
{
goto v___jp_1348_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1892_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1891_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1892_;
}
}
}
case 1:
{
lean_object* v___x_1893_; 
lean_inc(v_declName_1319_);
lean_inc(v_mvarId_1320_);
v___x_1893_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1320_, v_declName_1319_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
if (lean_obj_tag(v_a_1894_) == 1)
{
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1895_; 
v_val_1895_ = lean_ctor_get(v_a_1894_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v_a_1894_, 1);
v_mvarId_1320_ = v_val_1895_;
goto _start;
}
else
{
lean_object* v_val_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v_val_1897_ = lean_ctor_get(v_a_1894_, 0);
lean_inc(v_val_1897_);
lean_dec_ref_known(v_a_1894_, 1);
v___x_1898_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1899_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1898_);
if (v___x_1899_ == 0)
{
v_mvarId_1320_ = v_val_1897_;
goto _start;
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1902_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1901_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_dec_ref_known(v___x_1902_, 1);
v_mvarId_1320_ = v_val_1897_;
goto _start;
}
else
{
lean_dec(v_val_1897_);
lean_dec(v_declName_1319_);
return v___x_1902_;
}
}
}
}
else
{
lean_object* v___x_1904_; 
lean_dec(v_a_1894_);
lean_inc(v_mvarId_1320_);
v___x_1904_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
if (lean_obj_tag(v_a_1905_) == 1)
{
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1906_; 
v_val_1906_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_val_1906_);
lean_dec_ref_known(v_a_1905_, 1);
v___y_1330_ = v_val_1906_;
v___y_1331_ = v___x_1876_;
v___y_1332_ = v_a_1321_;
v___y_1333_ = v_a_1322_;
v___y_1334_ = v_a_1323_;
v___y_1335_ = v_a_1324_;
goto v___jp_1329_;
}
else
{
lean_object* v_val_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v_val_1907_ = lean_ctor_get(v_a_1905_, 0);
lean_inc(v_val_1907_);
lean_dec_ref_known(v_a_1905_, 1);
v___x_1908_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1909_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1908_);
if (v___x_1909_ == 0)
{
v___y_1330_ = v_val_1907_;
v___y_1331_ = v___x_1876_;
v___y_1332_ = v_a_1321_;
v___y_1333_ = v_a_1322_;
v___y_1334_ = v_a_1323_;
v___y_1335_ = v_a_1324_;
goto v___jp_1329_;
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1911_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1910_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_dec_ref_known(v___x_1911_, 1);
v___y_1330_ = v_val_1907_;
v___y_1331_ = v___x_1876_;
v___y_1332_ = v_a_1321_;
v___y_1333_ = v_a_1322_;
v___y_1334_ = v_a_1323_;
v___y_1335_ = v_a_1324_;
goto v___jp_1329_;
}
else
{
lean_dec(v_val_1907_);
lean_dec(v_declName_1319_);
return v___x_1911_;
}
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec(v_a_1905_);
lean_inc(v_mvarId_1320_);
v___x_1912_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1320_, v___x_1369_, v___x_1369_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
if (lean_obj_tag(v_a_1913_) == 1)
{
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_1914_; lean_object* v___x_1915_; 
v_val_1914_ = lean_ctor_get(v_a_1913_, 0);
lean_inc(v_val_1914_);
lean_dec_ref_known(v_a_1913_, 1);
v___x_1915_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_1914_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1915_;
}
else
{
lean_object* v_val_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_val_1916_ = lean_ctor_get(v_a_1913_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_a_1913_, 1);
v___x_1917_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1918_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_1916_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1921_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1920_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v___x_1922_; 
lean_dec_ref_known(v___x_1921_, 1);
v___x_1922_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_1916_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1922_;
}
else
{
lean_dec(v_val_1916_);
lean_dec(v_declName_1319_);
return v___x_1921_;
}
}
}
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_dec(v_a_1913_);
lean_dec(v_declName_1319_);
v___x_1923_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1924_, 0, v_mvarId_1320_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 7);
lean_ctor_set(v___x_1887_, 1, v___x_1924_);
lean_ctor_set(v___x_1887_, 0, v___x_1923_);
v___x_1926_ = v___x_1887_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1926_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1927_;
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1929_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1912_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1912_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1937_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1904_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1904_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1945_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1893_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1893_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
default: 
{
lean_del_object(v___x_1887_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_mvarId_1953_; 
v_mvarId_1953_ = lean_ctor_get(v_fst_1885_, 0);
lean_inc(v_mvarId_1953_);
lean_dec_ref_known(v_fst_1885_, 1);
v_mvarId_1320_ = v_mvarId_1953_;
goto _start;
}
else
{
lean_object* v_mvarId_1955_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_mvarId_1955_ = lean_ctor_get(v_fst_1885_, 0);
lean_inc(v_mvarId_1955_);
lean_dec_ref_known(v_fst_1885_, 1);
v___x_1956_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1957_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_1956_);
if (v___x_1957_ == 0)
{
v_mvarId_1320_ = v_mvarId_1955_;
goto _start;
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1960_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_1959_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_dec_ref_known(v___x_1960_, 1);
v_mvarId_1320_ = v_mvarId_1955_;
goto _start;
}
else
{
lean_dec(v_mvarId_1955_);
lean_dec(v_declName_1319_);
return v___x_1960_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1964_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1883_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1883_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
else
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1972_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1880_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1880_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1980_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1860_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1860_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1988_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1849_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1849_);
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
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_1996_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1838_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1838_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
goto v___jp_1351_;
}
else
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2005_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2004_);
if (v___x_2005_ == 0)
{
goto v___jp_1351_;
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2007_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2006_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_dec_ref_known(v___x_2007_, 1);
goto v___jp_1351_;
}
else
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2008_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1835_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1835_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
else
{
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
goto v___jp_1354_;
}
else
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2017_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2016_);
if (v___x_2017_ == 0)
{
goto v___jp_1354_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2018_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2019_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2018_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_dec_ref_known(v___x_2019_, 1);
goto v___jp_1354_;
}
else
{
return v___x_2019_;
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2020_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_1832_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_1832_);
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
else
{
v___y_1559_ = v_a_1829_;
goto v___jp_1558_;
}
}
}
else
{
lean_object* v___x_2030_; 
lean_inc(v_mvarId_1320_);
v___x_2030_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; uint8_t v___x_2032_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = lean_unbox(v_a_2031_);
lean_dec(v_a_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; 
lean_inc(v_mvarId_1320_);
v___x_2033_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; uint8_t v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = lean_unbox(v_a_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_inc(v_mvarId_1320_);
v___x_2036_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2036_, 1);
if (lean_obj_tag(v_a_2037_) == 1)
{
lean_dec(v_a_2034_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_2038_; 
v_val_2038_ = lean_ctor_get(v_a_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref_known(v_a_2037_, 1);
v_mvarId_1320_ = v_val_2038_;
goto _start;
}
else
{
lean_object* v_val_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; 
v_val_2040_ = lean_ctor_get(v_a_2037_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v_a_2037_, 1);
v___x_2041_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2042_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2041_);
if (v___x_2042_ == 0)
{
v_mvarId_1320_ = v_val_2040_;
goto _start;
}
else
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
v___x_2045_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2044_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_dec_ref_known(v___x_2045_, 1);
v_mvarId_1320_ = v_val_2040_;
goto _start;
}
else
{
lean_dec(v_val_2040_);
lean_dec(v_declName_1319_);
return v___x_2045_;
}
}
}
}
else
{
lean_object* v___x_2047_; 
lean_dec(v_a_2037_);
lean_inc(v_mvarId_1320_);
v___x_2047_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
if (lean_obj_tag(v_a_2048_) == 1)
{
lean_dec(v_a_2034_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_2049_; 
v_val_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v_a_2048_, 1);
v_mvarId_1320_ = v_val_2049_;
goto _start;
}
else
{
lean_object* v_val_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_val_2051_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v_a_2048_, 1);
v___x_2052_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2053_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2052_);
if (v___x_2053_ == 0)
{
v_mvarId_1320_ = v_val_2051_;
goto _start;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_2056_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2055_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_dec_ref_known(v___x_2056_, 1);
v_mvarId_1320_ = v_val_2051_;
goto _start;
}
else
{
lean_dec(v_val_2051_);
lean_dec(v_declName_1319_);
return v___x_2056_;
}
}
}
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_a_2048_);
lean_inc(v_mvarId_1320_);
v___x_2058_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1320_, v___x_1367_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2058_, 1);
if (lean_obj_tag(v_a_2059_) == 1)
{
lean_dec(v_a_2034_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_2060_; 
v_val_2060_ = lean_ctor_get(v_a_2059_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v_a_2059_, 1);
v_mvarId_1320_ = v_val_2060_;
goto _start;
}
else
{
lean_object* v_val_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_val_2062_ = lean_ctor_get(v_a_2059_, 0);
lean_inc(v_val_2062_);
lean_dec_ref_known(v_a_2059_, 1);
v___x_2063_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2064_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2063_);
if (v___x_2064_ == 0)
{
v_mvarId_1320_ = v_val_2062_;
goto _start;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__14);
v___x_2067_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2066_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_dec_ref_known(v___x_2067_, 1);
v_mvarId_1320_ = v_val_2062_;
goto _start;
}
else
{
lean_dec(v_val_2062_);
lean_dec(v_declName_1319_);
return v___x_2067_;
}
}
}
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; uint8_t v___x_2075_; uint8_t v___x_2076_; uint8_t v___x_2077_; uint8_t v___x_2078_; uint8_t v___x_2079_; uint8_t v___x_2080_; uint8_t v___x_2081_; uint8_t v___x_2082_; uint8_t v___x_2083_; uint8_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_dec(v_a_2059_);
v___x_2069_ = lean_unsigned_to_nat(100000u);
v___x_2070_ = lean_unsigned_to_nat(2u);
v___x_2071_ = 0;
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_2073_, 0, v___x_2069_);
lean_ctor_set(v___x_2073_, 1, v___x_2070_);
lean_ctor_set(v___x_2073_, 2, v___x_2072_);
v___x_2074_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3, v___x_2074_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 1, v___x_1367_);
v___x_2075_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 2, v___x_2075_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 3, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 4, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 5, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 6, v___x_2071_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 7, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 8, v___x_1367_);
v___x_2076_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 9, v___x_2076_);
v___x_2077_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 10, v___x_2077_);
v___x_2078_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 11, v___x_2078_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 12, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 13, v___x_1367_);
v___x_2079_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 14, v___x_2079_);
v___x_2080_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 15, v___x_2080_);
v___x_2081_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 16, v___x_2081_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 17, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 18, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 19, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 20, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 21, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 22, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 23, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 24, v___x_1367_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 25, v___x_1367_);
v___x_2082_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 26, v___x_2082_);
v___x_2083_ = lean_unbox(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 27, v___x_2083_);
v___x_2084_ = lean_unbox(v_a_2034_);
lean_dec(v_a_2034_);
lean_ctor_set_uint8(v___x_2073_, sizeof(void*)*3 + 28, v___x_2084_);
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__15));
v___x_2087_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17);
v___x_2088_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19);
v___x_2089_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*2, v___x_1367_);
v___x_2090_ = l_Lean_Options_empty;
v___x_2091_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_2073_, v___x_2086_, v___x_2089_, v___x_2090_, v_a_1321_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
v___x_2093_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
lean_inc(v_mvarId_1320_);
v___x_2094_ = l_Lean_Meta_simpTargetStar(v_mvarId_1320_, v_a_2092_, v___x_2086_, v___x_2072_, v___x_2093_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v_fst_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2197_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v_fst_2096_ = lean_ctor_get(v_a_2095_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_a_2095_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_a_2095_, 1);
lean_dec(v_unused_2198_);
v___x_2098_ = v_a_2095_;
v_isShared_2099_ = v_isSharedCheck_2197_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_fst_2096_);
lean_dec(v_a_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2197_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
switch(lean_obj_tag(v_fst_2096_))
{
case 0:
{
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
goto v___jp_1326_;
}
else
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2100_);
if (v___x_2101_ == 0)
{
goto v___jp_1326_;
}
else
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_2103_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2102_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_2103_;
}
}
}
case 1:
{
lean_object* v___x_2104_; 
lean_inc(v_declName_1319_);
lean_inc(v_mvarId_1320_);
v___x_2104_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1320_, v_declName_1319_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
if (lean_obj_tag(v_a_2105_) == 1)
{
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_2106_; 
v_val_2106_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_val_2106_);
lean_dec_ref_known(v_a_2105_, 1);
v_mvarId_1320_ = v_val_2106_;
goto _start;
}
else
{
lean_object* v_val_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v_val_2108_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_val_2108_);
lean_dec_ref_known(v_a_2105_, 1);
v___x_2109_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2109_);
if (v___x_2110_ == 0)
{
v_mvarId_1320_ = v_val_2108_;
goto _start;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_2113_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2112_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_dec_ref_known(v___x_2113_, 1);
v_mvarId_1320_ = v_val_2108_;
goto _start;
}
else
{
lean_dec(v_val_2108_);
lean_dec(v_declName_1319_);
return v___x_2113_;
}
}
}
}
else
{
lean_object* v___x_2115_; 
lean_dec(v_a_2105_);
lean_inc(v_mvarId_1320_);
v___x_2115_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2171_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2171_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2171_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2120_; lean_object* v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2125_; 
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
v_val_2120_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_a_2116_, 1);
if (v_hasTrace_1365_ == 0)
{
v___y_2122_ = v_a_1321_;
v___y_2123_ = v_a_1322_;
v___y_2124_ = v_a_1323_;
v___y_2125_ = v_a_1324_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2143_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2142_);
if (v___x_2143_ == 0)
{
v___y_2122_ = v_a_1321_;
v___y_2123_ = v_a_1322_;
v___y_2124_ = v_a_1323_;
v___y_2125_ = v_a_1324_;
goto v___jp_2121_;
}
else
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_2145_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2144_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_dec_ref_known(v___x_2145_, 1);
v___y_2122_ = v_a_1321_;
v___y_2123_ = v_a_1322_;
v___y_2124_ = v_a_1323_;
v___y_2125_ = v_a_1324_;
goto v___jp_2121_;
}
else
{
lean_dec(v_val_2120_);
lean_del_object(v___x_2118_);
lean_dec(v_declName_1319_);
return v___x_2145_;
}
}
}
v___jp_2121_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2126_ = lean_array_get_size(v_val_2120_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_nat_dec_lt(v___x_2085_, v___x_2126_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2130_; 
lean_dec(v_val_2120_);
lean_dec(v_declName_1319_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2127_);
v___x_2130_ = v___x_2118_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2127_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
else
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_nat_dec_le(v___x_2126_, v___x_2126_);
if (v___x_2132_ == 0)
{
if (v___x_2128_ == 0)
{
lean_object* v___x_2134_; 
lean_dec(v_val_2120_);
lean_dec(v_declName_1319_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2127_);
v___x_2134_ = v___x_2118_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2127_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
else
{
size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
lean_del_object(v___x_2118_);
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = lean_usize_of_nat(v___x_2126_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_declName_1319_, v_val_2120_, v___x_2136_, v___x_2137_, v___x_2127_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v_val_2120_);
return v___x_2138_;
}
}
else
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; 
lean_del_object(v___x_2118_);
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = lean_usize_of_nat(v___x_2126_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_declName_1319_, v_val_2120_, v___x_2139_, v___x_2140_, v___x_2127_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v_val_2120_);
return v___x_2141_;
}
}
}
}
else
{
lean_object* v___x_2146_; 
lean_del_object(v___x_2118_);
lean_dec(v_a_2116_);
lean_inc(v_mvarId_1320_);
v___x_2146_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1320_, v___x_1367_, v___x_1367_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
lean_inc(v_a_2147_);
lean_dec_ref_known(v___x_2146_, 1);
if (lean_obj_tag(v_a_2147_) == 1)
{
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_val_2148_; lean_object* v___x_2149_; 
v_val_2148_ = lean_ctor_get(v_a_2147_, 0);
lean_inc(v_val_2148_);
lean_dec_ref_known(v_a_2147_, 1);
v___x_2149_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_2148_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_2149_;
}
else
{
lean_object* v_val_2150_; lean_object* v___x_2151_; uint8_t v___x_2152_; 
v_val_2150_ = lean_ctor_get(v_a_2147_, 0);
lean_inc(v_val_2150_);
lean_dec_ref_known(v_a_2147_, 1);
v___x_2151_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2152_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_2150_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_2155_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2154_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v___x_2156_; 
lean_dec_ref_known(v___x_2155_, 1);
v___x_2156_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_1319_, v_val_2150_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_2156_;
}
else
{
lean_dec(v_val_2150_);
lean_dec(v_declName_1319_);
return v___x_2155_;
}
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec(v_a_2147_);
lean_dec(v_declName_1319_);
v___x_2157_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_mvarId_1320_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set_tag(v___x_2098_, 7);
lean_ctor_set(v___x_2098_, 1, v___x_2158_);
lean_ctor_set(v___x_2098_, 0, v___x_2157_);
v___x_2160_ = v___x_2098_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2157_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2160_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_2161_;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2163_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2146_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2146_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2172_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2115_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2115_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2180_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2104_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2104_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
default: 
{
lean_del_object(v___x_2098_);
lean_dec(v_mvarId_1320_);
if (v_hasTrace_1365_ == 0)
{
lean_object* v_mvarId_2188_; 
v_mvarId_2188_ = lean_ctor_get(v_fst_2096_, 0);
lean_inc(v_mvarId_2188_);
lean_dec_ref_known(v_fst_2096_, 1);
v_mvarId_1320_ = v_mvarId_2188_;
goto _start;
}
else
{
lean_object* v_mvarId_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_mvarId_2190_ = lean_ctor_get(v_fst_2096_, 0);
lean_inc(v_mvarId_2190_);
lean_dec_ref_known(v_fst_2096_, 1);
v___x_2191_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2192_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2191_);
if (v___x_2192_ == 0)
{
v_mvarId_1320_ = v_mvarId_2190_;
goto _start;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2195_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2194_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_dec_ref_known(v___x_2195_, 1);
v_mvarId_1320_ = v_mvarId_2190_;
goto _start;
}
else
{
lean_dec(v_mvarId_2190_);
lean_dec(v_declName_1319_);
return v___x_2195_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2199_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2094_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2094_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2207_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2091_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2091_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2034_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2215_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2058_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2058_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2034_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2223_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2047_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2047_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
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
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_a_2034_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2231_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2036_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2036_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_dec(v_a_2034_);
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
goto v___jp_1357_;
}
else
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2240_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2239_);
if (v___x_2240_ == 0)
{
goto v___jp_1357_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2242_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2241_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2242_) == 0)
{
lean_dec_ref_known(v___x_2242_, 1);
goto v___jp_1357_;
}
else
{
return v___x_2242_;
}
}
}
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2243_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2033_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2033_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
if (v_hasTrace_1365_ == 0)
{
goto v___jp_1360_;
}
else
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2252_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1363_, v___x_2251_);
if (v___x_2252_ == 0)
{
goto v___jp_1360_;
}
else
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2254_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_1366_, v___x_2253_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_dec_ref_known(v___x_2254_, 1);
goto v___jp_1360_;
}
else
{
return v___x_2254_;
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_dec(v_mvarId_1320_);
lean_dec(v_declName_1319_);
v_a_2255_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2030_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2030_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
v___jp_1326_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
return v___x_1328_;
}
v___jp_1329_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = lean_array_get_size(v___y_1330_);
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_nat_dec_lt(v___y_1331_, v___x_1336_);
if (v___x_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v___y_1330_);
lean_dec(v_declName_1319_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
return v___x_1339_;
}
else
{
uint8_t v___x_1340_; 
v___x_1340_ = lean_nat_dec_le(v___x_1336_, v___x_1336_);
if (v___x_1340_ == 0)
{
if (v___x_1338_ == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v___y_1330_);
lean_dec(v_declName_1319_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1337_);
return v___x_1341_;
}
else
{
size_t v___x_1342_; size_t v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((size_t)0ULL);
v___x_1343_ = lean_usize_of_nat(v___x_1336_);
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_declName_1319_, v___y_1330_, v___x_1342_, v___x_1343_, v___x_1337_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec_ref(v___y_1330_);
return v___x_1344_;
}
}
else
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = lean_usize_of_nat(v___x_1336_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_declName_1319_, v___y_1330_, v___x_1345_, v___x_1346_, v___x_1337_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec_ref(v___y_1330_);
return v___x_1347_;
}
}
}
v___jp_1348_:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
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
v___jp_1357_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
return v___x_1359_;
}
v___jp_1360_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_declName_2263_, lean_object* v_as_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
if (lean_obj_tag(v_as_2264_) == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_declName_2263_);
v___x_2270_ = lean_box(0);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
else
{
lean_object* v_head_2272_; lean_object* v_tail_2273_; lean_object* v___x_2274_; 
v_head_2272_ = lean_ctor_get(v_as_2264_, 0);
lean_inc(v_head_2272_);
v_tail_2273_ = lean_ctor_get(v_as_2264_, 1);
lean_inc(v_tail_2273_);
lean_dec_ref_known(v_as_2264_, 2);
lean_inc(v_declName_2263_);
v___x_2274_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2263_, v_head_2272_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_dec_ref_known(v___x_2274_, 1);
v_as_2264_ = v_tail_2273_;
goto _start;
}
else
{
lean_dec(v_tail_2273_);
lean_dec(v_declName_2263_);
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_declName_2276_, lean_object* v_as_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_declName_2276_, v_as_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4___boxed(lean_object* v_declName_2284_, lean_object* v_as_2285_, lean_object* v_i_2286_, lean_object* v_stop_2287_, lean_object* v_b_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
size_t v_i_boxed_2294_; size_t v_stop_boxed_2295_; lean_object* v_res_2296_; 
v_i_boxed_2294_ = lean_unbox_usize(v_i_2286_);
lean_dec(v_i_2286_);
v_stop_boxed_2295_ = lean_unbox_usize(v_stop_2287_);
lean_dec(v_stop_2287_);
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_declName_2284_, v_as_2285_, v_i_boxed_2294_, v_stop_boxed_2295_, v_b_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_as_2285_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2297_, lean_object* v_mvarId_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2297_, v_mvarId_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3(lean_object* v_00_u03b1_2305_, lean_object* v_x_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(v_x_2306_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2313_, lean_object* v_x_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3(v_00_u03b1_2313_, v_x_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2321_, uint8_t v_skipRealize_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v_env_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2325_ = lean_st_ref_get(v___y_2323_);
v_env_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_ref(v_env_2326_);
lean_dec(v___x_2325_);
v___x_2327_ = l_Lean_Environment_contains(v_env_2326_, v_constName_2321_, v_skipRealize_2322_);
v___x_2328_ = lean_box(v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2330_, lean_object* v_skipRealize_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v_skipRealize_boxed_2334_; lean_object* v_res_2335_; 
v_skipRealize_boxed_2334_ = lean_unbox(v_skipRealize_2331_);
v_res_2335_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2330_, v_skipRealize_boxed_2334_, v___y_2332_);
lean_dec(v___y_2332_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2336_, uint8_t v_skipRealize_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2336_, v_skipRealize_2337_, v___y_2341_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2344_, lean_object* v_skipRealize_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
uint8_t v_skipRealize_boxed_2351_; lean_object* v_res_2352_; 
v_skipRealize_boxed_2351_ = lean_unbox(v_skipRealize_2345_);
v_res_2352_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2344_, v_skipRealize_boxed_2351_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2353_, lean_object* v___x_2354_, lean_object* v___x_2355_, lean_object* v_snd_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___x_2362_; 
lean_inc_ref(v_snd_2353_);
v___x_2362_ = l_Lean_Meta_mkCongrArg(v_snd_2353_, v___x_2354_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v___x_2364_ = l_Lean_Expr_app___override(v_snd_2353_, v___x_2355_);
v___x_2365_ = l_Lean_MVarId_replaceTargetEq(v_snd_2356_, v___x_2364_, v_a_2363_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
return v___x_2365_;
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec(v_snd_2356_);
lean_dec_ref(v___x_2355_);
lean_dec_ref(v_snd_2353_);
v_a_2366_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2362_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2362_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2374_, lean_object* v___x_2375_, lean_object* v___x_2376_, lean_object* v_snd_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2374_, v___x_2375_, v___x_2376_, v_snd_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
return v_res_2383_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2393_ = l_Lean_stringToMessageData(v___x_2392_);
return v___x_2393_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2396_ = l_Lean_stringToMessageData(v___x_2395_);
return v___x_2396_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2399_ = l_Lean_stringToMessageData(v___x_2398_);
return v___x_2399_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2402_ = l_Lean_stringToMessageData(v___x_2401_);
return v___x_2402_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2405_ = l_Lean_stringToMessageData(v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2406_, lean_object* v___x_2407_, lean_object* v_cls_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; 
lean_inc(v_mvarId_2406_);
v___x_2414_ = l_Lean_MVarId_getType(v_mvarId_2406_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2416_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
v___x_2416_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2415_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v_fst_2418_; lean_object* v_snd_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2572_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref_known(v___x_2416_, 1);
v_fst_2418_ = lean_ctor_get(v_a_2417_, 0);
v_snd_2419_ = lean_ctor_get(v_a_2417_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_a_2417_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2421_ = v_a_2417_;
v_isShared_2422_ = v_isSharedCheck_2572_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_snd_2419_);
lean_inc(v_fst_2418_);
lean_dec(v_a_2417_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2572_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; lean_object* v___x_2428_; lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2571_; 
v___x_2423_ = l_Lean_Expr_getAppFn(v_fst_2418_);
v___x_2424_ = l_Lean_Expr_constName_x21(v___x_2423_);
v___x_2425_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2426_ = l_Lean_Name_str___override(v___x_2424_, v___x_2425_);
v___x_2427_ = 1;
lean_inc(v___x_2426_);
v___x_2428_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2426_, v___x_2427_, v___y_2412_);
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2571_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2571_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v_nargs_2433_; lean_object* v___x_2434_; lean_object* v_dummy_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; uint8_t v___y_2444_; lean_object* v___y_2445_; lean_object* v___y_2446_; lean_object* v___y_2447_; lean_object* v___y_2448_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; uint8_t v___x_2554_; 
v_nargs_2433_ = l_Lean_Expr_getAppNumArgs(v_fst_2418_);
v___x_2434_ = l_Lean_Expr_constLevels_x21(v___x_2423_);
lean_dec_ref(v___x_2423_);
v_dummy_2435_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
lean_inc(v_nargs_2433_);
v___x_2436_ = lean_mk_array(v_nargs_2433_, v_dummy_2435_);
v___x_2437_ = lean_unsigned_to_nat(1u);
v___x_2438_ = lean_nat_sub(v_nargs_2433_, v___x_2437_);
lean_dec(v_nargs_2433_);
v___x_2439_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2418_, v___x_2436_, v___x_2438_);
v___x_2554_ = lean_unbox(v_a_2429_);
lean_dec(v_a_2429_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v___x_2439_);
lean_dec(v___x_2434_);
lean_del_object(v___x_2431_);
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
lean_dec(v_cls_2408_);
v___x_2555_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2556_ = l_Lean_MessageData_ofName(v___x_2426_);
v___x_2557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v_mvarId_2406_);
v___x_2561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2561_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
v___y_2481_ = v___y_2409_;
v___y_2482_ = v___y_2410_;
v___y_2483_ = v___y_2411_;
v___y_2484_ = v___y_2412_;
goto v___jp_2480_;
}
v___jp_2440_:
{
lean_object* v___x_2449_; 
lean_inc(v___y_2448_);
lean_inc_ref(v___y_2447_);
lean_inc(v___y_2446_);
lean_inc_ref(v___y_2445_);
lean_inc_ref(v___y_2443_);
v___x_2449_ = lean_infer_type(v___y_2443_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2451_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2452_ = l_Lean_MVarId_define(v_mvarId_2406_, v___x_2451_, v_a_2450_, v___y_2443_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = l_Lean_Meta_intro1Core(v_a_2453_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v_fst_2456_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_fst_2456_);
v_snd_2457_ = lean_ctor_get(v_a_2455_, 1);
lean_inc_n(v_snd_2457_, 2);
lean_dec(v_a_2455_);
v___x_2458_ = l_Lean_Expr_appFn_x21(v___y_2442_);
lean_dec_ref(v___y_2442_);
v___x_2459_ = l_Lean_mkFVar(v_fst_2456_);
v___x_2460_ = l_Lean_Expr_app___override(v___x_2458_, v___x_2459_);
v___x_2461_ = l_Lean_mkAppN(v___y_2441_, v___x_2439_);
lean_dec_ref(v___x_2439_);
v___f_2462_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2462_, 0, v_snd_2419_);
lean_closure_set(v___f_2462_, 1, v___x_2461_);
lean_closure_set(v___f_2462_, 2, v___x_2460_);
lean_closure_set(v___f_2462_, 3, v_snd_2457_);
v___x_2463_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2457_, v___f_2462_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v___x_2463_;
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___x_2439_);
lean_dec(v_snd_2419_);
v_a_2464_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2454_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2454_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
else
{
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___x_2439_);
lean_dec(v_snd_2419_);
return v___x_2452_;
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v___x_2439_);
lean_dec(v_snd_2419_);
lean_dec(v_mvarId_2406_);
v_a_2472_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2449_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2449_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
v___jp_2480_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
lean_inc(v___x_2426_);
v___x_2485_ = l_Lean_mkConst(v___x_2426_, v___x_2434_);
lean_inc(v___y_2484_);
lean_inc_ref(v___y_2483_);
lean_inc(v___y_2482_);
lean_inc_ref(v___y_2481_);
lean_inc_ref(v___x_2485_);
v___x_2486_ = lean_infer_type(v___x_2485_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2488_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = l_Lean_Meta_instantiateForall(v_a_2487_, v___x_2439_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___x_2490_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2491_ = lean_unsigned_to_nat(3u);
v___x_2492_ = l_Lean_Expr_isAppOfArity(v_a_2489_, v___x_2490_, v___x_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_dec(v_a_2489_);
lean_dec_ref(v___x_2485_);
lean_dec_ref(v___x_2439_);
lean_dec(v_snd_2419_);
lean_dec(v_cls_2408_);
v___x_2493_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2494_ = l_Lean_MessageData_ofName(v___x_2426_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set_tag(v___x_2421_, 7);
lean_ctor_set(v___x_2421_, 1, v___x_2494_);
lean_ctor_set(v___x_2421_, 0, v___x_2493_);
v___x_2496_ = v___x_2421_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2500_; 
v___x_2497_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set_tag(v___x_2431_, 1);
lean_ctor_set(v___x_2431_, 0, v_mvarId_2406_);
v___x_2500_ = v___x_2431_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_mvarId_2406_);
v___x_2500_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2498_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2501_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v___x_2502_;
}
}
}
else
{
lean_object* v_options_2505_; lean_object* v_inheritedTraceOptions_2506_; uint8_t v_hasTrace_2507_; lean_object* v___x_2508_; lean_object* v_nargs_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_del_object(v___x_2431_);
lean_dec(v___x_2426_);
v_options_2505_ = lean_ctor_get(v___y_2483_, 2);
v_inheritedTraceOptions_2506_ = lean_ctor_get(v___y_2483_, 13);
v_hasTrace_2507_ = lean_ctor_get_uint8(v_options_2505_, sizeof(void*)*1);
v___x_2508_ = l_Lean_Expr_appArg_x21(v_a_2489_);
lean_dec(v_a_2489_);
v_nargs_2509_ = l_Lean_Expr_getAppNumArgs(v___x_2508_);
lean_inc(v_nargs_2509_);
v___x_2510_ = lean_mk_array(v_nargs_2509_, v_dummy_2435_);
v___x_2511_ = lean_nat_sub(v_nargs_2509_, v___x_2437_);
lean_dec(v_nargs_2509_);
lean_inc_ref(v___x_2508_);
v___x_2512_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2508_, v___x_2510_, v___x_2511_);
v___x_2513_ = lean_array_get_size(v___x_2512_);
v___x_2514_ = lean_nat_sub(v___x_2513_, v___x_2437_);
v___x_2515_ = lean_array_get(v___x_2407_, v___x_2512_, v___x_2514_);
lean_dec(v___x_2514_);
lean_dec_ref(v___x_2512_);
if (v_hasTrace_2507_ == 0)
{
lean_del_object(v___x_2421_);
lean_dec(v_cls_2408_);
v___y_2441_ = v___x_2485_;
v___y_2442_ = v___x_2508_;
v___y_2443_ = v___x_2515_;
v___y_2444_ = v___x_2492_;
v___y_2445_ = v___y_2481_;
v___y_2446_ = v___y_2482_;
v___y_2447_ = v___y_2483_;
v___y_2448_ = v___y_2484_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2516_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7));
lean_inc(v_cls_2408_);
v___x_2517_ = l_Lean_Name_append(v___x_2516_, v_cls_2408_);
v___x_2518_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2506_, v_options_2505_, v___x_2517_);
lean_dec(v___x_2517_);
if (v___x_2518_ == 0)
{
lean_del_object(v___x_2421_);
lean_dec(v_cls_2408_);
v___y_2441_ = v___x_2485_;
v___y_2442_ = v___x_2508_;
v___y_2443_ = v___x_2515_;
v___y_2444_ = v___x_2492_;
v___y_2445_ = v___y_2481_;
v___y_2446_ = v___y_2482_;
v___y_2447_ = v___y_2483_;
v___y_2448_ = v___y_2484_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2519_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2520_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2515_);
v___x_2521_ = l_Lean_inlineExpr(v___x_2515_, v___x_2520_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set_tag(v___x_2421_, 7);
lean_ctor_set(v___x_2421_, 1, v___x_2521_);
lean_ctor_set(v___x_2421_, 0, v___x_2519_);
v___x_2523_ = v___x_2421_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2519_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2524_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
lean_inc_ref(v___x_2508_);
v___x_2526_ = l_Lean_indentExpr(v___x_2508_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3(v_cls_2408_, v___x_2527_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_dec_ref_known(v___x_2528_, 1);
v___y_2441_ = v___x_2485_;
v___y_2442_ = v___x_2508_;
v___y_2443_ = v___x_2515_;
v___y_2444_ = v___x_2492_;
v___y_2445_ = v___y_2481_;
v___y_2446_ = v___y_2482_;
v___y_2447_ = v___y_2483_;
v___y_2448_ = v___y_2484_;
goto v___jp_2440_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v___x_2515_);
lean_dec_ref(v___x_2508_);
lean_dec_ref(v___x_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___x_2439_);
lean_dec(v_snd_2419_);
lean_dec(v_mvarId_2406_);
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2528_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
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
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec_ref(v___x_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___x_2439_);
lean_del_object(v___x_2431_);
lean_dec(v___x_2426_);
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
lean_dec(v_cls_2408_);
lean_dec(v_mvarId_2406_);
v_a_2538_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2488_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2488_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v___x_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec_ref(v___x_2439_);
lean_del_object(v___x_2431_);
lean_dec(v___x_2426_);
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
lean_dec(v_cls_2408_);
lean_dec(v_mvarId_2406_);
v_a_2546_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2486_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2486_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_cls_2408_);
lean_dec(v_mvarId_2406_);
v_a_2573_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2416_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2416_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_cls_2408_);
lean_dec(v_mvarId_2406_);
v_a_2581_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2414_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2414_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2589_, lean_object* v___x_2590_, lean_object* v_cls_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2589_, v___x_2590_, v_cls_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
lean_dec_ref(v___x_2590_);
return v_res_2597_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2599_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2600_ = l_Lean_stringToMessageData(v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2608_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2609_, 0, v_mvarId_2601_);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2612_, v_x_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___y_2615_);
lean_dec_ref(v___y_2614_);
lean_dec_ref(v_x_2613_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2620_, lean_object* v_mvarId_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_){
_start:
{
lean_object* v_options_2627_; lean_object* v_inheritedTraceOptions_2628_; uint8_t v_hasTrace_2629_; lean_object* v___x_2630_; lean_object* v_cls_2631_; lean_object* v___f_2632_; uint8_t v___x_2633_; 
v_options_2627_ = lean_ctor_get(v_a_2624_, 2);
v_inheritedTraceOptions_2628_ = lean_ctor_get(v_a_2624_, 13);
v_hasTrace_2629_ = lean_ctor_get_uint8(v_options_2627_, sizeof(void*)*1);
v___x_2630_ = l_Lean_instInhabitedExpr;
v_cls_2631_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
lean_inc(v_mvarId_2621_);
v___f_2632_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2632_, 0, v_mvarId_2621_);
lean_closure_set(v___f_2632_, 1, v___x_2630_);
lean_closure_set(v___f_2632_, 2, v_cls_2631_);
v___x_2633_ = lean_bool_not(v_hasTrace_2629_);
if (v___x_2633_ == 0)
{
lean_object* v___f_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___y_2638_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v_a_2641_; lean_object* v___y_2654_; uint8_t v___y_2655_; lean_object* v___y_2656_; lean_object* v_a_2657_; lean_object* v___y_2660_; lean_object* v___y_2661_; uint8_t v___y_2662_; lean_object* v_a_2663_; lean_object* v___y_2673_; uint8_t v___y_2674_; lean_object* v___y_2675_; lean_object* v_a_2676_; uint8_t v___y_2679_; uint8_t v_a_2713_; 
lean_inc(v_mvarId_2621_);
v___f_2634_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2634_, 0, v_mvarId_2621_);
v___x_2635_ = 1;
v___x_2636_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__0));
if (v_hasTrace_2629_ == 0)
{
v_a_2713_ = v_hasTrace_2629_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2727_; uint8_t v___x_2728_; 
v___x_2727_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_2728_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2628_, v_options_2627_, v___x_2727_);
if (v___x_2728_ == 0)
{
v_a_2713_ = v___x_2728_;
goto v___jp_2712_;
}
else
{
v___y_2679_ = v___x_2728_;
goto v___jp_2678_;
}
}
v___jp_2637_:
{
lean_object* v___x_2642_; double v___x_2643_; double v___x_2644_; double v___x_2645_; double v___x_2646_; double v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2642_ = lean_io_mono_nanos_now();
v___x_2643_ = lean_float_of_nat(v___y_2640_);
v___x_2644_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_2645_ = lean_float_div(v___x_2643_, v___x_2644_);
v___x_2646_ = lean_float_of_nat(v___x_2642_);
v___x_2647_ = lean_float_div(v___x_2646_, v___x_2644_);
v___x_2648_ = lean_box_float(v___x_2645_);
v___x_2649_ = lean_box_float(v___x_2647_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2648_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v_a_2641_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_cls_2631_, v___x_2635_, v___x_2636_, v_options_2627_, v___y_2639_, v___y_2638_, v___f_2634_, v___x_2651_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2652_;
}
v___jp_2653_:
{
lean_object* v___x_2658_; 
v___x_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_a_2657_);
v___y_2638_ = v___y_2656_;
v___y_2639_ = v___y_2655_;
v___y_2640_ = v___y_2654_;
v_a_2641_ = v___x_2658_;
goto v___jp_2637_;
}
v___jp_2659_:
{
lean_object* v___x_2664_; double v___x_2665_; double v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2664_ = lean_io_get_num_heartbeats();
v___x_2665_ = lean_float_of_nat(v___y_2660_);
v___x_2666_ = lean_float_of_nat(v___x_2664_);
v___x_2667_ = lean_box_float(v___x_2665_);
v___x_2668_ = lean_box_float(v___x_2666_);
v___x_2669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_a_2663_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_cls_2631_, v___x_2635_, v___x_2636_, v_options_2627_, v___y_2662_, v___y_2661_, v___f_2634_, v___x_2670_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2671_;
}
v___jp_2672_:
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_a_2676_);
v___y_2660_ = v___y_2673_;
v___y_2661_ = v___y_2675_;
v___y_2662_ = v___y_2674_;
v_a_2663_ = v___x_2677_;
goto v___jp_2659_;
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v_a_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2680_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_a_2625_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref(v___x_2680_);
v___x_2682_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2683_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_options_2627_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_io_mono_nanos_now();
v___x_2685_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2621_, v___f_2632_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2687_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2687_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2620_, v_a_2686_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2687_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set_tag(v___x_2690_, 1);
v___x_2693_ = v___x_2690_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_a_2688_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
v___y_2638_ = v_a_2681_;
v___y_2639_ = v___y_2679_;
v___y_2640_ = v___x_2684_;
v_a_2641_ = v___x_2693_;
goto v___jp_2637_;
}
}
}
else
{
lean_object* v_a_2696_; 
v_a_2696_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2687_, 1);
v___y_2654_ = v___x_2684_;
v___y_2655_ = v___y_2679_;
v___y_2656_ = v_a_2681_;
v_a_2657_ = v_a_2696_;
goto v___jp_2653_;
}
}
else
{
lean_object* v_a_2697_; 
lean_dec(v_declName_2620_);
v_a_2697_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2685_, 1);
v___y_2654_ = v___x_2684_;
v___y_2655_ = v___y_2679_;
v___y_2656_ = v_a_2681_;
v_a_2657_ = v_a_2697_;
goto v___jp_2653_;
}
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_io_get_num_heartbeats();
v___x_2699_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2621_, v___f_2632_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v___x_2701_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2701_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2620_, v_a_2700_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2701_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set_tag(v___x_2704_, 1);
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
v___y_2660_ = v___x_2698_;
v___y_2661_ = v_a_2681_;
v___y_2662_ = v___y_2679_;
v_a_2663_ = v___x_2707_;
goto v___jp_2659_;
}
}
}
else
{
lean_object* v_a_2710_; 
v_a_2710_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2701_, 1);
v___y_2673_ = v___x_2698_;
v___y_2674_ = v___y_2679_;
v___y_2675_ = v_a_2681_;
v_a_2676_ = v_a_2710_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2711_; 
lean_dec(v_declName_2620_);
v_a_2711_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2699_, 1);
v___y_2673_ = v___x_2698_;
v___y_2674_ = v___y_2679_;
v___y_2675_ = v_a_2681_;
v_a_2676_ = v_a_2711_;
goto v___jp_2672_;
}
}
}
v___jp_2712_:
{
lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2714_ = l_Lean_trace_profiler;
v___x_2715_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_options_2627_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_dec_ref(v___f_2634_);
v___x_2716_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2621_, v___f_2632_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2718_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2716_, 1);
v___x_2718_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2620_, v_a_2717_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2718_;
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2726_; 
lean_dec(v_declName_2620_);
v_a_2719_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2721_ = v___x_2716_;
v_isShared_2722_ = v_isSharedCheck_2726_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_a_2719_);
lean_dec(v___x_2716_);
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
else
{
v___y_2679_ = v_a_2713_;
goto v___jp_2678_;
}
}
}
else
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2621_, v___f_2632_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2620_, v_a_2730_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_);
return v___x_2731_;
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_declName_2620_);
v_a_2732_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2729_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2729_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2740_, lean_object* v_mvarId_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2740_, v_mvarId_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = l_Lean_Expr_hasMVar(v_e_2748_);
v___x_2752_ = lean_bool_not(v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; lean_object* v_mctx_2754_; lean_object* v___x_2755_; lean_object* v_fst_2756_; lean_object* v_snd_2757_; lean_object* v___x_2758_; lean_object* v_cache_2759_; lean_object* v_zetaDeltaFVarIds_2760_; lean_object* v_postponed_2761_; lean_object* v_diag_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2771_; 
v___x_2753_ = lean_st_ref_get(v___y_2749_);
v_mctx_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc_ref(v_mctx_2754_);
lean_dec(v___x_2753_);
v___x_2755_ = l_Lean_instantiateMVarsCore(v_mctx_2754_, v_e_2748_);
v_fst_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_fst_2756_);
v_snd_2757_ = lean_ctor_get(v___x_2755_, 1);
lean_inc(v_snd_2757_);
lean_dec_ref(v___x_2755_);
v___x_2758_ = lean_st_ref_take(v___y_2749_);
v_cache_2759_ = lean_ctor_get(v___x_2758_, 1);
v_zetaDeltaFVarIds_2760_ = lean_ctor_get(v___x_2758_, 2);
v_postponed_2761_ = lean_ctor_get(v___x_2758_, 3);
v_diag_2762_ = lean_ctor_get(v___x_2758_, 4);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v___x_2758_, 0);
lean_dec(v_unused_2772_);
v___x_2764_ = v___x_2758_;
v_isShared_2765_ = v_isSharedCheck_2771_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_diag_2762_);
lean_inc(v_postponed_2761_);
lean_inc(v_zetaDeltaFVarIds_2760_);
lean_inc(v_cache_2759_);
lean_dec(v___x_2758_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2771_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v_snd_2757_);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_snd_2757_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_cache_2759_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v_zetaDeltaFVarIds_2760_);
lean_ctor_set(v_reuseFailAlloc_2770_, 3, v_postponed_2761_);
lean_ctor_set(v_reuseFailAlloc_2770_, 4, v_diag_2762_);
v___x_2767_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_st_ref_set(v___y_2749_, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_fst_2756_);
return v___x_2769_;
}
}
}
else
{
lean_object* v___x_2773_; 
v___x_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2773_, 0, v_e_2748_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2774_, v___y_2775_);
lean_dec(v___y_2775_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2778_, v___y_2780_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2792_, uint8_t v_allowLevelAssignments_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2793_, v_k_2792_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2799_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2799_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2799_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2799_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2816_, lean_object* v_allowLevelAssignments_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2823_; lean_object* v_res_2824_; 
v_allowLevelAssignments_boxed_2823_ = lean_unbox(v_allowLevelAssignments_2817_);
v_res_2824_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2816_, v_allowLevelAssignments_boxed_2823_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2825_, lean_object* v_k_2826_, uint8_t v_allowLevelAssignments_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2826_, v_allowLevelAssignments_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2834_, lean_object* v_k_2835_, lean_object* v_allowLevelAssignments_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2842_; lean_object* v_res_2843_; 
v_allowLevelAssignments_boxed_2842_ = lean_unbox(v_allowLevelAssignments_2836_);
v_res_2843_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2834_, v_k_2835_, v_allowLevelAssignments_boxed_2842_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2844_, lean_object* v_e_2845_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = l_Lean_indentD(v_e_2845_);
v___x_2847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2844_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2848_, lean_object* v___x_2849_, lean_object* v_declName_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2848_, v___x_2849_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
v___x_2858_ = l_Lean_Expr_mvarId_x21(v_a_2857_);
v___x_2859_ = l_Lean_MVarId_intros(v___x_2858_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v_snd_2861_; lean_object* v___x_2862_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v_snd_2861_ = lean_ctor_get(v_a_2860_, 1);
lean_inc_n(v_snd_2861_, 2);
lean_dec(v_a_2860_);
v___x_2862_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2861_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; uint8_t v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
v___x_2864_ = lean_unbox(v_a_2863_);
lean_dec(v_a_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2861_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2850_, v_a_2866_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v___x_2868_; 
lean_dec_ref_known(v___x_2867_, 1);
v___x_2868_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2857_, v___y_2852_);
return v___x_2868_;
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec(v_a_2857_);
v_a_2869_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2867_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2867_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v_a_2857_);
lean_dec(v_declName_2850_);
v_a_2877_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2865_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2865_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
else
{
lean_object* v___x_2885_; 
lean_dec(v_snd_2861_);
lean_dec(v_declName_2850_);
v___x_2885_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2857_, v___y_2852_);
return v___x_2885_;
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_dec(v_snd_2861_);
lean_dec(v_a_2857_);
lean_dec(v_declName_2850_);
v_a_2886_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2862_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2862_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
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
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_dec(v_a_2857_);
lean_dec(v_declName_2850_);
v_a_2894_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2859_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2859_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_dec(v_declName_2850_);
return v___x_2856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2902_, lean_object* v___x_2903_, lean_object* v_declName_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2902_, v___x_2903_, v_declName_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
return v_res_2910_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2913_ = l_Lean_stringToMessageData(v___x_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2914_, lean_object* v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2921_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2922_ = l_Lean_indentExpr(v_type_2914_);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2925_, lean_object* v_x_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2925_, v_x_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_x_2926_);
return v_res_2932_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2933_){
_start:
{
if (lean_obj_tag(v_e_2933_) == 0)
{
uint8_t v___x_2934_; 
v___x_2934_ = 2;
return v___x_2934_;
}
else
{
lean_object* v_a_2935_; uint8_t v___x_2936_; 
v_a_2935_ = lean_ctor_get(v_e_2933_, 0);
v___x_2936_ = l_Lean_Expr_hasSyntheticSorry(v_a_2935_);
if (v___x_2936_ == 0)
{
uint8_t v___x_2937_; 
v___x_2937_ = 0;
return v___x_2937_;
}
else
{
uint8_t v___x_2938_; 
v___x_2938_ = 1;
return v___x_2938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2939_){
_start:
{
uint8_t v_res_2940_; lean_object* v_r_2941_; 
v_res_2940_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2939_);
lean_dec_ref(v_e_2939_);
v_r_2941_ = lean_box(v_res_2940_);
return v_r_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2942_, uint8_t v_collapsed_2943_, lean_object* v_tag_2944_, lean_object* v_opts_2945_, uint8_t v_clsEnabled_2946_, lean_object* v_oldTraces_2947_, lean_object* v_msg_2948_, lean_object* v_resStartStop_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v_fst_2955_; lean_object* v_snd_2956_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v_data_2960_; lean_object* v_fst_2971_; lean_object* v_snd_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; lean_object* v___y_2976_; lean_object* v_a_2977_; uint8_t v___y_2992_; double v___y_3023_; 
v_fst_2955_ = lean_ctor_get(v_resStartStop_2949_, 0);
lean_inc(v_fst_2955_);
v_snd_2956_ = lean_ctor_get(v_resStartStop_2949_, 1);
lean_inc(v_snd_2956_);
lean_dec_ref(v_resStartStop_2949_);
v_fst_2971_ = lean_ctor_get(v_snd_2956_, 0);
lean_inc(v_fst_2971_);
v_snd_2972_ = lean_ctor_get(v_snd_2956_, 1);
lean_inc(v_snd_2972_);
lean_dec(v_snd_2956_);
v___x_2973_ = l_Lean_trace_profiler;
v___x_2974_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_opts_2945_, v___x_2973_);
if (v___x_2974_ == 0)
{
v___y_2992_ = v___x_2974_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3028_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3029_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_opts_2945_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; double v___x_3032_; double v___x_3033_; double v___x_3034_; 
v___x_3030_ = l_Lean_trace_profiler_threshold;
v___x_3031_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(v_opts_2945_, v___x_3030_);
v___x_3032_ = lean_float_of_nat(v___x_3031_);
v___x_3033_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__3);
v___x_3034_ = lean_float_div(v___x_3032_, v___x_3033_);
v___y_3023_ = v___x_3034_;
goto v___jp_3022_;
}
else
{
lean_object* v___x_3035_; lean_object* v___x_3036_; double v___x_3037_; 
v___x_3035_ = l_Lean_trace_profiler_threshold;
v___x_3036_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(v_opts_2945_, v___x_3035_);
v___x_3037_ = lean_float_of_nat(v___x_3036_);
v___y_3023_ = v___x_3037_;
goto v___jp_3022_;
}
}
v___jp_2957_:
{
lean_object* v___x_2961_; 
lean_inc(v___y_2958_);
v___x_2961_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__2(v_oldTraces_2947_, v_data_2960_, v___y_2958_, v___y_2959_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v___x_2962_; 
lean_dec_ref_known(v___x_2961_, 1);
v___x_2962_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(v_fst_2955_);
return v___x_2962_;
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v_fst_2955_);
v_a_2963_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2961_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2961_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
v___jp_2975_:
{
uint8_t v_result_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; double v___x_2981_; lean_object* v_data_2982_; 
v_result_2978_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2955_);
v___x_2979_ = lean_box(v_result_2978_);
v___x_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
v___x_2981_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__0);
lean_inc_ref(v_tag_2944_);
lean_inc_ref(v___x_2980_);
lean_inc(v_cls_2942_);
v_data_2982_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2982_, 0, v_cls_2942_);
lean_ctor_set(v_data_2982_, 1, v___x_2980_);
lean_ctor_set(v_data_2982_, 2, v_tag_2944_);
lean_ctor_set_float(v_data_2982_, sizeof(void*)*3, v___x_2981_);
lean_ctor_set_float(v_data_2982_, sizeof(void*)*3 + 8, v___x_2981_);
lean_ctor_set_uint8(v_data_2982_, sizeof(void*)*3 + 16, v_collapsed_2943_);
if (v___x_2974_ == 0)
{
lean_dec_ref_known(v___x_2980_, 1);
lean_dec(v_snd_2972_);
lean_dec(v_fst_2971_);
lean_dec_ref(v_tag_2944_);
lean_dec(v_cls_2942_);
v___y_2958_ = v___y_2976_;
v___y_2959_ = v_a_2977_;
v_data_2960_ = v_data_2982_;
goto v___jp_2957_;
}
else
{
lean_object* v_data_2983_; double v___x_2984_; double v___x_2985_; 
lean_dec_ref_known(v_data_2982_, 3);
v_data_2983_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2983_, 0, v_cls_2942_);
lean_ctor_set(v_data_2983_, 1, v___x_2980_);
lean_ctor_set(v_data_2983_, 2, v_tag_2944_);
v___x_2984_ = lean_unbox_float(v_fst_2971_);
lean_dec(v_fst_2971_);
lean_ctor_set_float(v_data_2983_, sizeof(void*)*3, v___x_2984_);
v___x_2985_ = lean_unbox_float(v_snd_2972_);
lean_dec(v_snd_2972_);
lean_ctor_set_float(v_data_2983_, sizeof(void*)*3 + 8, v___x_2985_);
lean_ctor_set_uint8(v_data_2983_, sizeof(void*)*3 + 16, v_collapsed_2943_);
v___y_2958_ = v___y_2976_;
v___y_2959_ = v_a_2977_;
v_data_2960_ = v_data_2983_;
goto v___jp_2957_;
}
}
v___jp_2986_:
{
lean_object* v_ref_2987_; lean_object* v___x_2988_; 
v_ref_2987_ = lean_ctor_get(v___y_2952_, 5);
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2950_);
lean_inc(v_fst_2955_);
v___x_2988_ = lean_apply_6(v_msg_2948_, v_fst_2955_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, lean_box(0));
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v___y_2976_ = v_ref_2987_;
v_a_2977_ = v_a_2989_;
goto v___jp_2975_;
}
else
{
lean_object* v___x_2990_; 
lean_dec_ref_known(v___x_2988_, 1);
v___x_2990_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___closed__2);
v___y_2976_ = v_ref_2987_;
v_a_2977_ = v___x_2990_;
goto v___jp_2975_;
}
}
v___jp_2991_:
{
if (v_clsEnabled_2946_ == 0)
{
if (v___y_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v_traceState_2994_; lean_object* v_env_2995_; lean_object* v_nextMacroScope_2996_; lean_object* v_ngen_2997_; lean_object* v_auxDeclNGen_2998_; lean_object* v_cache_2999_; lean_object* v_messages_3000_; lean_object* v_infoState_3001_; lean_object* v_snapshotTasks_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_snd_2972_);
lean_dec(v_fst_2971_);
lean_dec_ref(v_msg_2948_);
lean_dec_ref(v_tag_2944_);
lean_dec(v_cls_2942_);
v___x_2993_ = lean_st_ref_take(v___y_2953_);
v_traceState_2994_ = lean_ctor_get(v___x_2993_, 4);
v_env_2995_ = lean_ctor_get(v___x_2993_, 0);
v_nextMacroScope_2996_ = lean_ctor_get(v___x_2993_, 1);
v_ngen_2997_ = lean_ctor_get(v___x_2993_, 2);
v_auxDeclNGen_2998_ = lean_ctor_get(v___x_2993_, 3);
v_cache_2999_ = lean_ctor_get(v___x_2993_, 5);
v_messages_3000_ = lean_ctor_get(v___x_2993_, 6);
v_infoState_3001_ = lean_ctor_get(v___x_2993_, 7);
v_snapshotTasks_3002_ = lean_ctor_get(v___x_2993_, 8);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3004_ = v___x_2993_;
v_isShared_3005_ = v_isSharedCheck_3021_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_snapshotTasks_3002_);
lean_inc(v_infoState_3001_);
lean_inc(v_messages_3000_);
lean_inc(v_cache_2999_);
lean_inc(v_traceState_2994_);
lean_inc(v_auxDeclNGen_2998_);
lean_inc(v_ngen_2997_);
lean_inc(v_nextMacroScope_2996_);
lean_inc(v_env_2995_);
lean_dec(v___x_2993_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3021_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
uint64_t v_tid_3006_; lean_object* v_traces_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3020_; 
v_tid_3006_ = lean_ctor_get_uint64(v_traceState_2994_, sizeof(void*)*1);
v_traces_3007_ = lean_ctor_get(v_traceState_2994_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v_traceState_2994_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3009_ = v_traceState_2994_;
v_isShared_3010_ = v_isSharedCheck_3020_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_traces_3007_);
lean_dec(v_traceState_2994_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3020_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3011_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2947_, v_traces_3007_);
lean_dec_ref(v_traces_3007_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 0, v___x_3011_);
v___x_3013_ = v___x_3009_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3011_);
lean_ctor_set_uint64(v_reuseFailAlloc_3019_, sizeof(void*)*1, v_tid_3006_);
v___x_3013_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3015_; 
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 4, v___x_3013_);
v___x_3015_ = v___x_3004_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_env_2995_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_nextMacroScope_2996_);
lean_ctor_set(v_reuseFailAlloc_3018_, 2, v_ngen_2997_);
lean_ctor_set(v_reuseFailAlloc_3018_, 3, v_auxDeclNGen_2998_);
lean_ctor_set(v_reuseFailAlloc_3018_, 4, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3018_, 5, v_cache_2999_);
lean_ctor_set(v_reuseFailAlloc_3018_, 6, v_messages_3000_);
lean_ctor_set(v_reuseFailAlloc_3018_, 7, v_infoState_3001_);
lean_ctor_set(v_reuseFailAlloc_3018_, 8, v_snapshotTasks_3002_);
v___x_3015_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_st_ref_set(v___y_2953_, v___x_3015_);
v___x_3017_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__3___redArg(v_fst_2955_);
return v___x_3017_;
}
}
}
}
}
else
{
goto v___jp_2986_;
}
}
else
{
goto v___jp_2986_;
}
}
v___jp_3022_:
{
double v___x_3024_; double v___x_3025_; double v___x_3026_; uint8_t v___x_3027_; 
v___x_3024_ = lean_unbox_float(v_snd_2972_);
v___x_3025_ = lean_unbox_float(v_fst_2971_);
v___x_3026_ = lean_float_sub(v___x_3024_, v___x_3025_);
v___x_3027_ = lean_float_decLt(v___y_3023_, v___x_3026_);
v___y_2992_ = v___x_3027_;
goto v___jp_2991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_3038_, lean_object* v_collapsed_3039_, lean_object* v_tag_3040_, lean_object* v_opts_3041_, lean_object* v_clsEnabled_3042_, lean_object* v_oldTraces_3043_, lean_object* v_msg_3044_, lean_object* v_resStartStop_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
uint8_t v_collapsed_boxed_3051_; uint8_t v_clsEnabled_boxed_3052_; lean_object* v_res_3053_; 
v_collapsed_boxed_3051_ = lean_unbox(v_collapsed_3039_);
v_clsEnabled_boxed_3052_ = lean_unbox(v_clsEnabled_3042_);
v_res_3053_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_3038_, v_collapsed_boxed_3051_, v_tag_3040_, v_opts_3041_, v_clsEnabled_boxed_3052_, v_oldTraces_3043_, v_msg_3044_, v_resStartStop_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec_ref(v_opts_3041_);
return v_res_3053_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_3056_ = l_Lean_stringToMessageData(v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_3059_ = l_Lean_stringToMessageData(v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_3060_, lean_object* v_type_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_options_3067_; lean_object* v_inheritedTraceOptions_3068_; uint8_t v_hasTrace_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___f_3076_; lean_object* v___x_3077_; lean_object* v___f_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_options_3067_ = lean_ctor_get(v_a_3064_, 2);
v_inheritedTraceOptions_3068_ = lean_ctor_get(v_a_3064_, 13);
v_hasTrace_3069_ = lean_ctor_get_uint8(v_options_3067_, sizeof(void*)*1);
v___x_3070_ = 0;
lean_inc(v_declName_3060_);
v___x_3071_ = l_Lean_MessageData_ofConstName(v_declName_3060_, v___x_3070_);
v___x_3072_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v___x_3071_);
v___x_3074_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_3076_, 0, v___x_3075_);
v___x_3077_ = lean_box(0);
lean_inc_ref(v_type_3061_);
v___f_3078_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_3078_, 0, v_type_3061_);
lean_closure_set(v___f_3078_, 1, v___x_3077_);
lean_closure_set(v___f_3078_, 2, v_declName_3060_);
v___x_3079_ = lean_box(v___x_3070_);
v___x_3080_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_3080_, 0, lean_box(0));
lean_closure_set(v___x_3080_, 1, v___f_3078_);
lean_closure_set(v___x_3080_, 2, v___x_3079_);
v___x_3081_ = lean_bool_not(v_hasTrace_3069_);
if (v___x_3081_ == 0)
{
lean_object* v___f_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___y_3087_; lean_object* v___y_3088_; uint8_t v___y_3089_; lean_object* v_a_3090_; lean_object* v___y_3103_; uint8_t v___y_3104_; lean_object* v___y_3105_; lean_object* v_a_3106_; uint8_t v___y_3116_; uint8_t v_a_3158_; 
v___f_3082_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3082_, 0, v_type_3061_);
v___x_3083_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_3084_ = 1;
v___x_3085_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___closed__0));
if (v_hasTrace_3069_ == 0)
{
v_a_3158_ = v_hasTrace_3069_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3178_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_3179_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3068_, v_options_3067_, v___x_3178_);
if (v___x_3179_ == 0)
{
v_a_3158_ = v___x_3179_;
goto v___jp_3157_;
}
else
{
v___y_3116_ = v___x_3179_;
goto v___jp_3115_;
}
}
v___jp_3086_:
{
lean_object* v___x_3091_; double v___x_3092_; double v___x_3093_; double v___x_3094_; double v___x_3095_; double v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3091_ = lean_io_mono_nanos_now();
v___x_3092_ = lean_float_of_nat(v___y_3088_);
v___x_3093_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_3094_ = lean_float_div(v___x_3092_, v___x_3093_);
v___x_3095_ = lean_float_of_nat(v___x_3091_);
v___x_3096_ = lean_float_div(v___x_3095_, v___x_3093_);
v___x_3097_ = lean_box_float(v___x_3094_);
v___x_3098_ = lean_box_float(v___x_3096_);
v___x_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3100_, 0, v_a_3090_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_3083_, v___x_3084_, v___x_3085_, v_options_3067_, v___y_3089_, v___y_3087_, v___f_3082_, v___x_3100_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v___x_3101_;
}
v___jp_3102_:
{
lean_object* v___x_3107_; double v___x_3108_; double v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3107_ = lean_io_get_num_heartbeats();
v___x_3108_ = lean_float_of_nat(v___y_3105_);
v___x_3109_ = lean_float_of_nat(v___x_3107_);
v___x_3110_ = lean_box_float(v___x_3108_);
v___x_3111_ = lean_box_float(v___x_3109_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3110_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v_a_3106_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_3083_, v___x_3084_, v___x_3085_, v_options_3067_, v___y_3104_, v___y_3103_, v___f_3082_, v___x_3113_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
return v___x_3114_;
}
v___jp_3115_:
{
lean_object* v___x_3117_; lean_object* v_a_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___redArg(v_a_3065_);
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref(v___x_3117_);
v___x_3119_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3120_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_options_3067_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
v___x_3121_ = lean_io_mono_nanos_now();
v___x_3122_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3080_, v___f_3076_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 1);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
v___y_3087_ = v_a_3118_;
v___y_3088_ = v___x_3121_;
v___y_3089_ = v___y_3116_;
v_a_3090_ = v___x_3128_;
goto v___jp_3086_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_a_3131_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3122_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3122_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
lean_ctor_set_tag(v___x_3133_, 0);
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
v___y_3087_ = v_a_3118_;
v___y_3088_ = v___x_3121_;
v___y_3089_ = v___y_3116_;
v_a_3090_ = v___x_3136_;
goto v___jp_3086_;
}
}
}
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = lean_io_get_num_heartbeats();
v___x_3140_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3080_, v___f_3076_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
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
lean_ctor_set_tag(v___x_3143_, 1);
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
v___y_3103_ = v_a_3118_;
v___y_3104_ = v___y_3116_;
v___y_3105_ = v___x_3139_;
v_a_3106_ = v___x_3146_;
goto v___jp_3102_;
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
lean_ctor_set_tag(v___x_3151_, 0);
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
v___y_3103_ = v_a_3118_;
v___y_3104_ = v___y_3116_;
v___y_3105_ = v___x_3139_;
v_a_3106_ = v___x_3154_;
goto v___jp_3102_;
}
}
}
}
}
v___jp_3157_:
{
lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3159_ = l_Lean_trace_profiler;
v___x_3160_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_options_3067_, v___x_3159_);
if (v___x_3160_ == 0)
{
lean_object* v___x_3161_; 
lean_dec_ref(v___f_3082_);
v___x_3161_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3080_, v___f_3076_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3161_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3161_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
else
{
v___y_3116_ = v_a_3158_;
goto v___jp_3115_;
}
}
}
else
{
lean_object* v___x_3180_; 
lean_dec_ref(v_type_3061_);
v___x_3180_ = l_Lean_Meta_mapErrorImp___redArg(v___x_3080_, v___f_3076_, v_a_3062_, v_a_3063_, v_a_3064_, v_a_3065_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
v_a_3189_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3180_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3180_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3197_, lean_object* v_type_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3197_, v_type_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
return v_res_3204_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_3205_, lean_object* v_n_3206_, lean_object* v_x_3207_){
_start:
{
uint8_t v___x_3208_; 
v___x_3208_ = l_Lean_Environment_hasExposedBody(v_env_3205_, v_n_3206_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_env_3209_, lean_object* v_n_3210_, lean_object* v_x_3211_){
_start:
{
uint8_t v_res_3212_; lean_object* v_r_3213_; 
v_res_3212_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(v_env_3209_, v_n_3210_, v_x_3211_);
lean_dec_ref(v_x_3211_);
v_r_3213_ = lean_box(v_res_3212_);
return v_r_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3214_, lean_object* v_x_3215_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 0)
{
lean_object* v_k_3216_; lean_object* v_v_3217_; lean_object* v_l_3218_; lean_object* v_r_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v_k_3216_ = lean_ctor_get(v_x_3215_, 1);
v_v_3217_ = lean_ctor_get(v_x_3215_, 2);
v_l_3218_ = lean_ctor_get(v_x_3215_, 3);
v_r_3219_ = lean_ctor_get(v_x_3215_, 4);
v___x_3220_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3214_, v_l_3218_);
lean_inc(v_v_3217_);
lean_inc(v_k_3216_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_k_3216_);
lean_ctor_set(v___x_3221_, 1, v_v_3217_);
v___x_3222_ = lean_array_push(v___x_3220_, v___x_3221_);
v_init_3214_ = v___x_3222_;
v_x_3215_ = v_r_3219_;
goto _start;
}
else
{
return v_init_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3224_, lean_object* v_x_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3224_, v_x_3225_);
lean_dec(v_x_3225_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(lean_object* v_env_3229_, lean_object* v_s_3230_){
_start:
{
lean_object* v___f_3231_; lean_object* v___x_3232_; lean_object* v_all_3233_; lean_object* v___x_3234_; lean_object* v_exported_3235_; lean_object* v___x_3236_; 
v___f_3231_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3231_, 0, v_env_3229_);
v___x_3232_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v_all_3233_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3232_, v_s_3230_);
v___x_3234_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3231_, v_s_3230_);
v_exported_3235_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v___x_3232_, v___x_3234_);
lean_dec(v___x_3234_);
lean_inc_ref(v_exported_3235_);
v___x_3236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3236_, 0, v_exported_3235_);
lean_ctor_set(v___x_3236_, 1, v_exported_3235_);
lean_ctor_set(v___x_3236_, 2, v_all_3233_);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___f_3249_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3250_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3251_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_));
v___x_3252_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3250_, v___x_3251_, v___f_3249_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2____boxed(lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2_();
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(lean_object* v_init_3255_, lean_object* v_t_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0_spec__0(v_init_3255_, v_t_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3258_, lean_object* v_t_3259_){
_start:
{
lean_object* v_res_3260_; 
v_res_3260_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_3225328890____hygCtx___hyg_2__spec__0(v_init_3258_, v_t_3259_);
lean_dec(v_t_3259_);
return v_res_3260_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3261_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
return v___x_3263_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3266_, lean_object* v_declNames_3267_, lean_object* v_recArgPos_3268_, lean_object* v_fixedParamPerms_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_levelParams_3273_; lean_object* v_declName_3274_; lean_object* v_type_3275_; lean_object* v_value_3276_; lean_object* v___x_3277_; 
v_levelParams_3273_ = lean_ctor_get(v_preDef_3266_, 1);
lean_inc(v_levelParams_3273_);
v_declName_3274_ = lean_ctor_get(v_preDef_3266_, 3);
lean_inc_n(v_declName_3274_, 2);
v_type_3275_ = lean_ctor_get(v_preDef_3266_, 6);
lean_inc_ref(v_type_3275_);
v_value_3276_ = lean_ctor_get(v_preDef_3266_, 7);
lean_inc_ref(v_value_3276_);
lean_dec_ref(v_preDef_3266_);
v___x_3277_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3274_, v_a_3270_, v_a_3271_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3307_; 
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3307_ == 0)
{
lean_object* v_unused_3308_; 
v_unused_3308_ = lean_ctor_get(v___x_3277_, 0);
lean_dec(v_unused_3308_);
v___x_3279_ = v___x_3277_;
v_isShared_3280_ = v_isSharedCheck_3307_;
goto v_resetjp_3278_;
}
else
{
lean_dec(v___x_3277_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3307_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v_env_3282_; lean_object* v_nextMacroScope_3283_; lean_object* v_ngen_3284_; lean_object* v_auxDeclNGen_3285_; lean_object* v_traceState_3286_; lean_object* v_messages_3287_; lean_object* v_infoState_3288_; lean_object* v_snapshotTasks_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3305_; 
v___x_3281_ = lean_st_ref_take(v_a_3271_);
v_env_3282_ = lean_ctor_get(v___x_3281_, 0);
v_nextMacroScope_3283_ = lean_ctor_get(v___x_3281_, 1);
v_ngen_3284_ = lean_ctor_get(v___x_3281_, 2);
v_auxDeclNGen_3285_ = lean_ctor_get(v___x_3281_, 3);
v_traceState_3286_ = lean_ctor_get(v___x_3281_, 4);
v_messages_3287_ = lean_ctor_get(v___x_3281_, 6);
v_infoState_3288_ = lean_ctor_get(v___x_3281_, 7);
v_snapshotTasks_3289_ = lean_ctor_get(v___x_3281_, 8);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3305_ == 0)
{
lean_object* v_unused_3306_; 
v_unused_3306_ = lean_ctor_get(v___x_3281_, 5);
lean_dec(v_unused_3306_);
v___x_3291_ = v___x_3281_;
v_isShared_3292_ = v_isSharedCheck_3305_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_snapshotTasks_3289_);
lean_inc(v_infoState_3288_);
lean_inc(v_messages_3287_);
lean_inc(v_traceState_3286_);
lean_inc(v_auxDeclNGen_3285_);
lean_inc(v_ngen_3284_);
lean_inc(v_nextMacroScope_3283_);
lean_inc(v_env_3282_);
lean_dec(v___x_3281_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3305_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3298_; 
v___x_3293_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3274_);
v___x_3294_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3294_, 0, v_declName_3274_);
lean_ctor_set(v___x_3294_, 1, v_levelParams_3273_);
lean_ctor_set(v___x_3294_, 2, v_type_3275_);
lean_ctor_set(v___x_3294_, 3, v_value_3276_);
lean_ctor_set(v___x_3294_, 4, v_recArgPos_3268_);
lean_ctor_set(v___x_3294_, 5, v_declNames_3267_);
lean_ctor_set(v___x_3294_, 6, v_fixedParamPerms_3269_);
v___x_3295_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3293_, v_env_3282_, v_declName_3274_, v___x_3294_);
v___x_3296_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 5, v___x_3296_);
lean_ctor_set(v___x_3291_, 0, v___x_3295_);
v___x_3298_ = v___x_3291_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_nextMacroScope_3283_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_ngen_3284_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_auxDeclNGen_3285_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v_traceState_3286_);
lean_ctor_set(v_reuseFailAlloc_3304_, 5, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3304_, 6, v_messages_3287_);
lean_ctor_set(v_reuseFailAlloc_3304_, 7, v_infoState_3288_);
lean_ctor_set(v_reuseFailAlloc_3304_, 8, v_snapshotTasks_3289_);
v___x_3298_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3299_ = lean_st_ref_set(v_a_3271_, v___x_3298_);
v___x_3300_ = lean_box(0);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 0, v___x_3300_);
v___x_3302_ = v___x_3279_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
else
{
lean_dec_ref(v_value_3276_);
lean_dec_ref(v_type_3275_);
lean_dec(v_declName_3274_);
lean_dec(v_levelParams_3273_);
lean_dec_ref(v_fixedParamPerms_3269_);
lean_dec(v_recArgPos_3268_);
lean_dec_ref(v_declNames_3267_);
return v___x_3277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3309_, lean_object* v_declNames_3310_, lean_object* v_recArgPos_3311_, lean_object* v_fixedParamPerms_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3309_, v_declNames_3310_, v_recArgPos_3311_, v_fixedParamPerms_3312_, v_a_3313_, v_a_3314_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3317_, lean_object* v_k_3318_, uint8_t v_cleanupAnnotations_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v___f_3325_; uint8_t v___x_3326_; uint8_t v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___f_3325_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3325_, 0, v_k_3318_);
v___x_3326_ = 1;
v___x_3327_ = 0;
v___x_3328_ = lean_box(0);
v___x_3329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3317_, v___x_3326_, v___x_3327_, v___x_3326_, v___x_3327_, v___x_3328_, v___f_3325_, v_cleanupAnnotations_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3329_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3329_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
v_a_3338_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3329_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3329_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3346_, lean_object* v_k_3347_, lean_object* v_cleanupAnnotations_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3354_; lean_object* v_res_3355_; 
v_cleanupAnnotations_boxed_3354_ = lean_unbox(v_cleanupAnnotations_3348_);
v_res_3355_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3346_, v_k_3347_, v_cleanupAnnotations_boxed_3354_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3356_, lean_object* v_e_3357_, lean_object* v_k_3358_, uint8_t v_cleanupAnnotations_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3357_, v_k_3358_, v_cleanupAnnotations_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3366_, lean_object* v_e_3367_, lean_object* v_k_3368_, lean_object* v_cleanupAnnotations_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3375_; lean_object* v_res_3376_; 
v_cleanupAnnotations_boxed_3375_ = lean_unbox(v_cleanupAnnotations_3369_);
v_res_3376_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3366_, v_e_3367_, v_k_3368_, v_cleanupAnnotations_boxed_3375_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3377_, uint8_t v_isExporting_3378_, lean_object* v___x_3379_, lean_object* v___y_3380_, lean_object* v___x_3381_, lean_object* v_a_x3f_3382_){
_start:
{
lean_object* v___x_3384_; lean_object* v_env_3385_; lean_object* v_nextMacroScope_3386_; lean_object* v_ngen_3387_; lean_object* v_auxDeclNGen_3388_; lean_object* v_traceState_3389_; lean_object* v_messages_3390_; lean_object* v_infoState_3391_; lean_object* v_snapshotTasks_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3417_; 
v___x_3384_ = lean_st_ref_take(v___y_3377_);
v_env_3385_ = lean_ctor_get(v___x_3384_, 0);
v_nextMacroScope_3386_ = lean_ctor_get(v___x_3384_, 1);
v_ngen_3387_ = lean_ctor_get(v___x_3384_, 2);
v_auxDeclNGen_3388_ = lean_ctor_get(v___x_3384_, 3);
v_traceState_3389_ = lean_ctor_get(v___x_3384_, 4);
v_messages_3390_ = lean_ctor_get(v___x_3384_, 6);
v_infoState_3391_ = lean_ctor_get(v___x_3384_, 7);
v_snapshotTasks_3392_ = lean_ctor_get(v___x_3384_, 8);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3384_, 5);
lean_dec(v_unused_3418_);
v___x_3394_ = v___x_3384_;
v_isShared_3395_ = v_isSharedCheck_3417_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_snapshotTasks_3392_);
lean_inc(v_infoState_3391_);
lean_inc(v_messages_3390_);
lean_inc(v_traceState_3389_);
lean_inc(v_auxDeclNGen_3388_);
lean_inc(v_ngen_3387_);
lean_inc(v_nextMacroScope_3386_);
lean_inc(v_env_3385_);
lean_dec(v___x_3384_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3417_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3396_; lean_object* v___x_3398_; 
v___x_3396_ = l_Lean_Environment_setExporting(v_env_3385_, v_isExporting_3378_);
if (v_isShared_3395_ == 0)
{
lean_ctor_set(v___x_3394_, 5, v___x_3379_);
lean_ctor_set(v___x_3394_, 0, v___x_3396_);
v___x_3398_ = v___x_3394_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3396_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_nextMacroScope_3386_);
lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_ngen_3387_);
lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_auxDeclNGen_3388_);
lean_ctor_set(v_reuseFailAlloc_3416_, 4, v_traceState_3389_);
lean_ctor_set(v_reuseFailAlloc_3416_, 5, v___x_3379_);
lean_ctor_set(v_reuseFailAlloc_3416_, 6, v_messages_3390_);
lean_ctor_set(v_reuseFailAlloc_3416_, 7, v_infoState_3391_);
lean_ctor_set(v_reuseFailAlloc_3416_, 8, v_snapshotTasks_3392_);
v___x_3398_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v_mctx_3401_; lean_object* v_zetaDeltaFVarIds_3402_; lean_object* v_postponed_3403_; lean_object* v_diag_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3414_; 
v___x_3399_ = lean_st_ref_set(v___y_3377_, v___x_3398_);
v___x_3400_ = lean_st_ref_take(v___y_3380_);
v_mctx_3401_ = lean_ctor_get(v___x_3400_, 0);
v_zetaDeltaFVarIds_3402_ = lean_ctor_get(v___x_3400_, 2);
v_postponed_3403_ = lean_ctor_get(v___x_3400_, 3);
v_diag_3404_ = lean_ctor_get(v___x_3400_, 4);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v___x_3400_, 1);
lean_dec(v_unused_3415_);
v___x_3406_ = v___x_3400_;
v_isShared_3407_ = v_isSharedCheck_3414_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_diag_3404_);
lean_inc(v_postponed_3403_);
lean_inc(v_zetaDeltaFVarIds_3402_);
lean_inc(v_mctx_3401_);
lean_dec(v___x_3400_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3414_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 1, v___x_3381_);
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_mctx_3401_);
lean_ctor_set(v_reuseFailAlloc_3413_, 1, v___x_3381_);
lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_zetaDeltaFVarIds_3402_);
lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_postponed_3403_);
lean_ctor_set(v_reuseFailAlloc_3413_, 4, v_diag_3404_);
v___x_3409_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3410_ = lean_st_ref_set(v___y_3380_, v___x_3409_);
v___x_3411_ = lean_box(0);
v___x_3412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
return v___x_3412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3419_, lean_object* v_isExporting_3420_, lean_object* v___x_3421_, lean_object* v___y_3422_, lean_object* v___x_3423_, lean_object* v_a_x3f_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v_isExporting_boxed_3426_; lean_object* v_res_3427_; 
v_isExporting_boxed_3426_ = lean_unbox(v_isExporting_3420_);
v_res_3427_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3419_, v_isExporting_boxed_3426_, v___x_3421_, v___y_3422_, v___x_3423_, v_a_x3f_3424_);
lean_dec(v_a_x3f_3424_);
lean_dec(v___y_3422_);
lean_dec(v___y_3419_);
return v_res_3427_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3429_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
lean_ctor_set(v___x_3429_, 2, v___x_3428_);
lean_ctor_set(v___x_3429_, 3, v___x_3428_);
lean_ctor_set(v___x_3429_, 4, v___x_3428_);
lean_ctor_set(v___x_3429_, 5, v___x_3428_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3430_, uint8_t v_isExporting_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
lean_object* v___x_3437_; lean_object* v_env_3438_; uint8_t v_isExporting_3439_; uint8_t v___y_3506_; lean_object* v___x_3508_; uint8_t v_isModule_3509_; uint8_t v___x_3510_; 
v___x_3437_ = lean_st_ref_get(v___y_3435_);
v_env_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc_ref(v_env_3438_);
lean_dec(v___x_3437_);
v_isExporting_3439_ = lean_ctor_get_uint8(v_env_3438_, sizeof(void*)*8);
v___x_3508_ = l_Lean_Environment_header(v_env_3438_);
lean_dec_ref(v_env_3438_);
v_isModule_3509_ = lean_ctor_get_uint8(v___x_3508_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3508_);
v___x_3510_ = lean_bool_not(v_isModule_3509_);
if (v___x_3510_ == 0)
{
if (v_isExporting_3439_ == 0)
{
if (v_isExporting_3431_ == 0)
{
lean_object* v___x_3511_; 
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
v___x_3511_ = lean_apply_5(v_x_3430_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, lean_box(0));
return v___x_3511_;
}
else
{
goto v___jp_3440_;
}
}
else
{
v___y_3506_ = v_isExporting_3431_;
goto v___jp_3505_;
}
}
else
{
v___y_3506_ = v___x_3510_;
goto v___jp_3505_;
}
v___jp_3440_:
{
lean_object* v___x_3441_; lean_object* v_env_3442_; lean_object* v_nextMacroScope_3443_; lean_object* v_ngen_3444_; lean_object* v_auxDeclNGen_3445_; lean_object* v_traceState_3446_; lean_object* v_messages_3447_; lean_object* v_infoState_3448_; lean_object* v_snapshotTasks_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3503_; 
v___x_3441_ = lean_st_ref_take(v___y_3435_);
v_env_3442_ = lean_ctor_get(v___x_3441_, 0);
v_nextMacroScope_3443_ = lean_ctor_get(v___x_3441_, 1);
v_ngen_3444_ = lean_ctor_get(v___x_3441_, 2);
v_auxDeclNGen_3445_ = lean_ctor_get(v___x_3441_, 3);
v_traceState_3446_ = lean_ctor_get(v___x_3441_, 4);
v_messages_3447_ = lean_ctor_get(v___x_3441_, 6);
v_infoState_3448_ = lean_ctor_get(v___x_3441_, 7);
v_snapshotTasks_3449_ = lean_ctor_get(v___x_3441_, 8);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3503_ == 0)
{
lean_object* v_unused_3504_; 
v_unused_3504_ = lean_ctor_get(v___x_3441_, 5);
lean_dec(v_unused_3504_);
v___x_3451_ = v___x_3441_;
v_isShared_3452_ = v_isSharedCheck_3503_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_snapshotTasks_3449_);
lean_inc(v_infoState_3448_);
lean_inc(v_messages_3447_);
lean_inc(v_traceState_3446_);
lean_inc(v_auxDeclNGen_3445_);
lean_inc(v_ngen_3444_);
lean_inc(v_nextMacroScope_3443_);
lean_inc(v_env_3442_);
lean_dec(v___x_3441_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3503_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3453_ = l_Lean_Environment_setExporting(v_env_3442_, v_isExporting_3431_);
v___x_3454_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3452_ == 0)
{
lean_ctor_set(v___x_3451_, 5, v___x_3454_);
lean_ctor_set(v___x_3451_, 0, v___x_3453_);
v___x_3456_ = v___x_3451_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_nextMacroScope_3443_);
lean_ctor_set(v_reuseFailAlloc_3502_, 2, v_ngen_3444_);
lean_ctor_set(v_reuseFailAlloc_3502_, 3, v_auxDeclNGen_3445_);
lean_ctor_set(v_reuseFailAlloc_3502_, 4, v_traceState_3446_);
lean_ctor_set(v_reuseFailAlloc_3502_, 5, v___x_3454_);
lean_ctor_set(v_reuseFailAlloc_3502_, 6, v_messages_3447_);
lean_ctor_set(v_reuseFailAlloc_3502_, 7, v_infoState_3448_);
lean_ctor_set(v_reuseFailAlloc_3502_, 8, v_snapshotTasks_3449_);
v___x_3456_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v_mctx_3459_; lean_object* v_zetaDeltaFVarIds_3460_; lean_object* v_postponed_3461_; lean_object* v_diag_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3500_; 
v___x_3457_ = lean_st_ref_set(v___y_3435_, v___x_3456_);
v___x_3458_ = lean_st_ref_take(v___y_3433_);
v_mctx_3459_ = lean_ctor_get(v___x_3458_, 0);
v_zetaDeltaFVarIds_3460_ = lean_ctor_get(v___x_3458_, 2);
v_postponed_3461_ = lean_ctor_get(v___x_3458_, 3);
v_diag_3462_ = lean_ctor_get(v___x_3458_, 4);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3458_, 1);
lean_dec(v_unused_3501_);
v___x_3464_ = v___x_3458_;
v_isShared_3465_ = v_isSharedCheck_3500_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_diag_3462_);
lean_inc(v_postponed_3461_);
lean_inc(v_zetaDeltaFVarIds_3460_);
lean_inc(v_mctx_3459_);
lean_dec(v___x_3458_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3500_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3466_; lean_object* v___x_3468_; 
v___x_3466_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v___x_3466_);
v___x_3468_ = v___x_3464_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_mctx_3459_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v___x_3466_);
lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_zetaDeltaFVarIds_3460_);
lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_postponed_3461_);
lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_diag_3462_);
v___x_3468_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
lean_object* v___x_3469_; lean_object* v_r_3470_; 
v___x_3469_ = lean_st_ref_set(v___y_3433_, v___x_3468_);
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
v_r_3470_ = lean_apply_5(v_x_3430_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, lean_box(0));
if (lean_obj_tag(v_r_3470_) == 0)
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3487_; 
v_a_3471_ = lean_ctor_get(v_r_3470_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_r_3470_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3473_ = v_r_3470_;
v_isShared_3474_ = v_isSharedCheck_3487_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v_r_3470_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3487_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
lean_inc(v_a_3471_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set_tag(v___x_3473_, 1);
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v___x_3477_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3435_, v_isExporting_3439_, v___x_3454_, v___y_3433_, v___x_3466_, v___x_3476_);
lean_dec_ref(v___x_3476_);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3485_);
v___x_3479_ = v___x_3477_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_dec(v___x_3477_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_a_3471_);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3471_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
v_a_3488_ = lean_ctor_get(v_r_3470_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v_r_3470_, 1);
v___x_3489_ = lean_box(0);
v___x_3490_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3435_, v_isExporting_3439_, v___x_3454_, v___y_3433_, v___x_3466_, v___x_3489_);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v___x_3490_, 0);
lean_dec(v_unused_3498_);
v___x_3492_ = v___x_3490_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_dec(v___x_3490_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set_tag(v___x_3492_, 1);
lean_ctor_set(v___x_3492_, 0, v_a_3488_);
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3488_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
}
}
}
v___jp_3505_:
{
if (v___y_3506_ == 0)
{
goto v___jp_3440_;
}
else
{
lean_object* v___x_3507_; 
lean_inc(v___y_3435_);
lean_inc_ref(v___y_3434_);
lean_inc(v___y_3433_);
lean_inc_ref(v___y_3432_);
v___x_3507_ = lean_apply_5(v_x_3430_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, lean_box(0));
return v___x_3507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3512_, lean_object* v_isExporting_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
uint8_t v_isExporting_boxed_3519_; lean_object* v_res_3520_; 
v_isExporting_boxed_3519_ = lean_unbox(v_isExporting_3513_);
v_res_3520_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3512_, v_isExporting_boxed_3519_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3521_, uint8_t v_when_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
if (v_when_3522_ == 0)
{
lean_object* v___x_3528_; 
lean_inc(v___y_3526_);
lean_inc_ref(v___y_3525_);
lean_inc(v___y_3524_);
lean_inc_ref(v___y_3523_);
v___x_3528_ = lean_apply_5(v_x_3521_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, lean_box(0));
return v___x_3528_;
}
else
{
uint8_t v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = 0;
v___x_3530_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3521_, v___x_3529_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_);
return v___x_3530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3531_, lean_object* v_when_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
uint8_t v_when_boxed_3538_; lean_object* v_res_3539_; 
v_when_boxed_3538_ = lean_unbox(v_when_3532_);
v_res_3539_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3531_, v_when_boxed_3538_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
if (lean_obj_tag(v_a_3540_) == 0)
{
lean_object* v___x_3542_; 
v___x_3542_ = l_List_reverse___redArg(v_a_3541_);
return v___x_3542_;
}
else
{
lean_object* v_head_3543_; lean_object* v_tail_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3553_; 
v_head_3543_ = lean_ctor_get(v_a_3540_, 0);
v_tail_3544_ = lean_ctor_get(v_a_3540_, 1);
v_isSharedCheck_3553_ = !lean_is_exclusive(v_a_3540_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3546_ = v_a_3540_;
v_isShared_3547_ = v_isSharedCheck_3553_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_tail_3544_);
lean_inc(v_head_3543_);
lean_dec(v_a_3540_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3553_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3548_ = l_Lean_mkLevelParam(v_head_3543_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 1, v_a_3541_);
lean_ctor_set(v___x_3546_, 0, v___x_3548_);
v___x_3550_ = v___x_3546_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v___x_3548_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_a_3541_);
v___x_3550_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
v_a_3540_ = v_tail_3544_;
v_a_3541_ = v___x_3550_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3554_, lean_object* v_declName_3555_, lean_object* v_name_3556_, lean_object* v_xs_3557_, lean_object* v_body_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v___x_3564_; lean_object* v_us_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3564_ = lean_box(0);
lean_inc(v_levelParams_3554_);
v_us_3565_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3554_, v___x_3564_);
lean_inc(v_declName_3555_);
v___x_3566_ = l_Lean_mkConst(v_declName_3555_, v_us_3565_);
v___x_3567_ = l_Lean_mkAppN(v___x_3566_, v_xs_3557_);
v___x_3568_ = l_Lean_Meta_mkEq(v___x_3567_, v_body_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; lean_object* v___x_3572_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc_n(v_a_3569_, 2);
lean_dec_ref_known(v___x_3568_, 1);
v___x_3570_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3570_, 0, v_declName_3555_);
lean_closure_set(v___x_3570_, 1, v_a_3569_);
v___x_3571_ = 1;
v___x_3572_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3570_, v___x_3571_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_a_3573_; uint8_t v___x_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; 
v_a_3573_ = lean_ctor_get(v___x_3572_, 0);
lean_inc(v_a_3573_);
lean_dec_ref_known(v___x_3572_, 1);
v___x_3574_ = 0;
v___x_3575_ = 1;
v___x_3576_ = l_Lean_Meta_mkForallFVars(v_xs_3557_, v_a_3569_, v___x_3574_, v___x_3571_, v___x_3571_, v___x_3575_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3576_) == 0)
{
lean_object* v_a_3577_; lean_object* v___x_3578_; 
v_a_3577_ = lean_ctor_get(v___x_3576_, 0);
lean_inc(v_a_3577_);
lean_dec_ref_known(v___x_3576_, 1);
v___x_3578_ = l_Lean_Meta_letToHave(v_a_3577_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3578_) == 0)
{
lean_object* v_a_3579_; lean_object* v___x_3580_; 
v_a_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc(v_a_3579_);
lean_dec_ref_known(v___x_3578_, 1);
v___x_3580_ = l_Lean_Meta_mkLambdaFVars(v_xs_3557_, v_a_3573_, v___x_3574_, v___x_3571_, v___x_3574_, v___x_3571_, v___x_3575_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
lean_inc(v_a_3581_);
lean_dec_ref_known(v___x_3580_, 1);
lean_inc_n(v_name_3556_, 2);
v___x_3582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3582_, 0, v_name_3556_);
lean_ctor_set(v___x_3582_, 1, v_levelParams_3554_);
lean_ctor_set(v___x_3582_, 2, v_a_3579_);
v___x_3583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3583_, 0, v_name_3556_);
lean_ctor_set(v___x_3583_, 1, v___x_3564_);
v___x_3584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3582_);
lean_ctor_set(v___x_3584_, 1, v_a_3581_);
lean_ctor_set(v___x_3584_, 2, v___x_3583_);
v___x_3585_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
v___x_3586_ = l_Lean_addDecl(v___x_3585_, v___x_3574_, v___y_3561_, v___y_3562_);
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v___x_3587_; 
lean_dec_ref_known(v___x_3586_, 1);
v___x_3587_ = l_Lean_inferDefEqAttr(v_name_3556_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
return v___x_3587_;
}
else
{
lean_dec(v_name_3556_);
return v___x_3586_;
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec(v_a_3579_);
lean_dec(v_name_3556_);
lean_dec(v_levelParams_3554_);
v_a_3588_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3580_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3580_);
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
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_a_3573_);
lean_dec(v_name_3556_);
lean_dec(v_levelParams_3554_);
v_a_3596_ = lean_ctor_get(v___x_3578_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3578_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3578_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3578_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec(v_a_3573_);
lean_dec(v_name_3556_);
lean_dec(v_levelParams_3554_);
v_a_3604_ = lean_ctor_get(v___x_3576_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3576_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3576_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_a_3569_);
lean_dec(v_name_3556_);
lean_dec(v_levelParams_3554_);
v_a_3612_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3572_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3572_);
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
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_name_3556_);
lean_dec(v_declName_3555_);
lean_dec(v_levelParams_3554_);
v_a_3620_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3568_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3568_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3628_, lean_object* v_declName_3629_, lean_object* v_name_3630_, lean_object* v_xs_3631_, lean_object* v_body_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3628_, v_declName_3629_, v_name_3630_, v_xs_3631_, v_body_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec_ref(v_xs_3631_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3639_, lean_object* v_k_3640_, uint8_t v_v_3641_){
_start:
{
lean_object* v_map_3642_; uint8_t v_hasTrace_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3657_; 
v_map_3642_ = lean_ctor_get(v_o_3639_, 0);
v_hasTrace_3643_ = lean_ctor_get_uint8(v_o_3639_, sizeof(void*)*1);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_o_3639_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3645_ = v_o_3639_;
v_isShared_3646_ = v_isSharedCheck_3657_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_map_3642_);
lean_dec(v_o_3639_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3657_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
v___x_3647_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3647_, 0, v_v_3641_);
lean_inc(v_k_3640_);
v___x_3648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3640_, v___x_3647_, v_map_3642_);
if (v_hasTrace_3643_ == 0)
{
lean_object* v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3652_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7));
v___x_3650_ = l_Lean_Name_isPrefixOf(v___x_3649_, v_k_3640_);
lean_dec(v_k_3640_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3648_);
v___x_3652_ = v___x_3645_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3648_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
lean_ctor_set_uint8(v___x_3652_, sizeof(void*)*1, v___x_3650_);
return v___x_3652_;
}
}
else
{
lean_object* v___x_3655_; 
lean_dec(v_k_3640_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3648_);
v___x_3655_ = v___x_3645_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3648_);
lean_ctor_set_uint8(v_reuseFailAlloc_3656_, sizeof(void*)*1, v_hasTrace_3643_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3658_, lean_object* v_k_3659_, lean_object* v_v_3660_){
_start:
{
uint8_t v_v_boxed_3661_; lean_object* v_res_3662_; 
v_v_boxed_3661_ = lean_unbox(v_v_3660_);
v_res_3662_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3658_, v_k_3659_, v_v_boxed_3661_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3663_, lean_object* v_opt_3664_, uint8_t v_val_3665_){
_start:
{
lean_object* v_name_3666_; lean_object* v___x_3667_; 
v_name_3666_ = lean_ctor_get(v_opt_3664_, 0);
lean_inc(v_name_3666_);
lean_dec_ref(v_opt_3664_);
v___x_3667_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3663_, v_name_3666_, v_val_3665_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3668_, lean_object* v_opt_3669_, lean_object* v_val_3670_){
_start:
{
uint8_t v_val_boxed_3671_; lean_object* v_res_3672_; 
v_val_boxed_3671_ = lean_unbox(v_val_3670_);
v_res_3672_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3668_, v_opt_3669_, v_val_boxed_3671_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3673_, lean_object* v_info_3674_, lean_object* v_name_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___x_3681_; lean_object* v_levelParams_3682_; lean_object* v_value_3683_; lean_object* v_fileName_3684_; lean_object* v_fileMap_3685_; lean_object* v_options_3686_; lean_object* v_currRecDepth_3687_; lean_object* v_ref_3688_; lean_object* v_currNamespace_3689_; lean_object* v_openDecls_3690_; lean_object* v_initHeartbeats_3691_; lean_object* v_maxHeartbeats_3692_; lean_object* v_quotContext_3693_; lean_object* v_currMacroScope_3694_; lean_object* v_cancelTk_x3f_3695_; uint8_t v_suppressElabErrors_3696_; lean_object* v_inheritedTraceOptions_3697_; lean_object* v_env_3698_; lean_object* v___f_3699_; uint8_t v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; lean_object* v_fileName_3706_; lean_object* v_fileMap_3707_; lean_object* v_currRecDepth_3708_; lean_object* v_ref_3709_; lean_object* v_currNamespace_3710_; lean_object* v_openDecls_3711_; lean_object* v_initHeartbeats_3712_; lean_object* v_maxHeartbeats_3713_; lean_object* v_quotContext_3714_; lean_object* v_currMacroScope_3715_; lean_object* v_cancelTk_x3f_3716_; uint8_t v_suppressElabErrors_3717_; lean_object* v_inheritedTraceOptions_3718_; lean_object* v___y_3719_; uint8_t v___y_3725_; uint8_t v___x_3747_; 
v___x_3681_ = lean_st_ref_get(v_a_3679_);
v_levelParams_3682_ = lean_ctor_get(v_info_3674_, 1);
lean_inc(v_levelParams_3682_);
v_value_3683_ = lean_ctor_get(v_info_3674_, 3);
lean_inc_ref(v_value_3683_);
lean_dec_ref(v_info_3674_);
v_fileName_3684_ = lean_ctor_get(v_a_3678_, 0);
v_fileMap_3685_ = lean_ctor_get(v_a_3678_, 1);
v_options_3686_ = lean_ctor_get(v_a_3678_, 2);
v_currRecDepth_3687_ = lean_ctor_get(v_a_3678_, 3);
v_ref_3688_ = lean_ctor_get(v_a_3678_, 5);
v_currNamespace_3689_ = lean_ctor_get(v_a_3678_, 6);
v_openDecls_3690_ = lean_ctor_get(v_a_3678_, 7);
v_initHeartbeats_3691_ = lean_ctor_get(v_a_3678_, 8);
v_maxHeartbeats_3692_ = lean_ctor_get(v_a_3678_, 9);
v_quotContext_3693_ = lean_ctor_get(v_a_3678_, 10);
v_currMacroScope_3694_ = lean_ctor_get(v_a_3678_, 11);
v_cancelTk_x3f_3695_ = lean_ctor_get(v_a_3678_, 12);
v_suppressElabErrors_3696_ = lean_ctor_get_uint8(v_a_3678_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3697_ = lean_ctor_get(v_a_3678_, 13);
v_env_3698_ = lean_ctor_get(v___x_3681_, 0);
lean_inc_ref(v_env_3698_);
lean_dec(v___x_3681_);
v___f_3699_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3699_, 0, v_levelParams_3682_);
lean_closure_set(v___f_3699_, 1, v_declName_3673_);
lean_closure_set(v___f_3699_, 2, v_name_3675_);
v___x_3700_ = 0;
v___x_3701_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3686_);
v___x_3702_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3686_, v___x_3701_, v___x_3700_);
v___x_3703_ = l_Lean_diagnostics;
v___x_3704_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v___x_3702_, v___x_3703_);
v___x_3747_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3698_);
lean_dec_ref(v_env_3698_);
if (v___x_3747_ == 0)
{
if (v___x_3704_ == 0)
{
uint8_t v___x_3748_; 
v___x_3748_ = 1;
v___y_3725_ = v___x_3748_;
goto v___jp_3724_;
}
else
{
v___y_3725_ = v___x_3747_;
goto v___jp_3724_;
}
}
else
{
v___y_3725_ = v___x_3704_;
goto v___jp_3724_;
}
v___jp_3705_:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3720_ = l_Lean_maxRecDepth;
v___x_3721_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2_spec__5(v___x_3702_, v___x_3720_);
lean_inc_ref(v_inheritedTraceOptions_3718_);
lean_inc(v_cancelTk_x3f_3716_);
lean_inc(v_currMacroScope_3715_);
lean_inc(v_quotContext_3714_);
lean_inc(v_maxHeartbeats_3713_);
lean_inc(v_initHeartbeats_3712_);
lean_inc(v_openDecls_3711_);
lean_inc(v_currNamespace_3710_);
lean_inc(v_ref_3709_);
lean_inc(v_currRecDepth_3708_);
lean_inc_ref(v_fileMap_3707_);
lean_inc_ref(v_fileName_3706_);
v___x_3722_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3722_, 0, v_fileName_3706_);
lean_ctor_set(v___x_3722_, 1, v_fileMap_3707_);
lean_ctor_set(v___x_3722_, 2, v___x_3702_);
lean_ctor_set(v___x_3722_, 3, v_currRecDepth_3708_);
lean_ctor_set(v___x_3722_, 4, v___x_3721_);
lean_ctor_set(v___x_3722_, 5, v_ref_3709_);
lean_ctor_set(v___x_3722_, 6, v_currNamespace_3710_);
lean_ctor_set(v___x_3722_, 7, v_openDecls_3711_);
lean_ctor_set(v___x_3722_, 8, v_initHeartbeats_3712_);
lean_ctor_set(v___x_3722_, 9, v_maxHeartbeats_3713_);
lean_ctor_set(v___x_3722_, 10, v_quotContext_3714_);
lean_ctor_set(v___x_3722_, 11, v_currMacroScope_3715_);
lean_ctor_set(v___x_3722_, 12, v_cancelTk_x3f_3716_);
lean_ctor_set(v___x_3722_, 13, v_inheritedTraceOptions_3718_);
lean_ctor_set_uint8(v___x_3722_, sizeof(void*)*14, v___x_3704_);
lean_ctor_set_uint8(v___x_3722_, sizeof(void*)*14 + 1, v_suppressElabErrors_3717_);
v___x_3723_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3683_, v___f_3699_, v___x_3700_, v_a_3676_, v_a_3677_, v___x_3722_, v___y_3719_);
lean_dec_ref_known(v___x_3722_, 14);
return v___x_3723_;
}
v___jp_3724_:
{
uint8_t v___x_3726_; 
v___x_3726_ = lean_bool_not(v___y_3725_);
if (v___x_3726_ == 0)
{
v_fileName_3706_ = v_fileName_3684_;
v_fileMap_3707_ = v_fileMap_3685_;
v_currRecDepth_3708_ = v_currRecDepth_3687_;
v_ref_3709_ = v_ref_3688_;
v_currNamespace_3710_ = v_currNamespace_3689_;
v_openDecls_3711_ = v_openDecls_3690_;
v_initHeartbeats_3712_ = v_initHeartbeats_3691_;
v_maxHeartbeats_3713_ = v_maxHeartbeats_3692_;
v_quotContext_3714_ = v_quotContext_3693_;
v_currMacroScope_3715_ = v_currMacroScope_3694_;
v_cancelTk_x3f_3716_ = v_cancelTk_x3f_3695_;
v_suppressElabErrors_3717_ = v_suppressElabErrors_3696_;
v_inheritedTraceOptions_3718_ = v_inheritedTraceOptions_3697_;
v___y_3719_ = v_a_3679_;
goto v___jp_3705_;
}
else
{
lean_object* v___x_3727_; lean_object* v_env_3728_; lean_object* v_nextMacroScope_3729_; lean_object* v_ngen_3730_; lean_object* v_auxDeclNGen_3731_; lean_object* v_traceState_3732_; lean_object* v_messages_3733_; lean_object* v_infoState_3734_; lean_object* v_snapshotTasks_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3745_; 
v___x_3727_ = lean_st_ref_take(v_a_3679_);
v_env_3728_ = lean_ctor_get(v___x_3727_, 0);
v_nextMacroScope_3729_ = lean_ctor_get(v___x_3727_, 1);
v_ngen_3730_ = lean_ctor_get(v___x_3727_, 2);
v_auxDeclNGen_3731_ = lean_ctor_get(v___x_3727_, 3);
v_traceState_3732_ = lean_ctor_get(v___x_3727_, 4);
v_messages_3733_ = lean_ctor_get(v___x_3727_, 6);
v_infoState_3734_ = lean_ctor_get(v___x_3727_, 7);
v_snapshotTasks_3735_ = lean_ctor_get(v___x_3727_, 8);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; 
v_unused_3746_ = lean_ctor_get(v___x_3727_, 5);
lean_dec(v_unused_3746_);
v___x_3737_ = v___x_3727_;
v_isShared_3738_ = v_isSharedCheck_3745_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_snapshotTasks_3735_);
lean_inc(v_infoState_3734_);
lean_inc(v_messages_3733_);
lean_inc(v_traceState_3732_);
lean_inc(v_auxDeclNGen_3731_);
lean_inc(v_ngen_3730_);
lean_inc(v_nextMacroScope_3729_);
lean_inc(v_env_3728_);
lean_dec(v___x_3727_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3745_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3739_ = l_Lean_Kernel_enableDiag(v_env_3728_, v___x_3704_);
v___x_3740_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 5, v___x_3740_);
lean_ctor_set(v___x_3737_, 0, v___x_3739_);
v___x_3742_ = v___x_3737_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v_nextMacroScope_3729_);
lean_ctor_set(v_reuseFailAlloc_3744_, 2, v_ngen_3730_);
lean_ctor_set(v_reuseFailAlloc_3744_, 3, v_auxDeclNGen_3731_);
lean_ctor_set(v_reuseFailAlloc_3744_, 4, v_traceState_3732_);
lean_ctor_set(v_reuseFailAlloc_3744_, 5, v___x_3740_);
lean_ctor_set(v_reuseFailAlloc_3744_, 6, v_messages_3733_);
lean_ctor_set(v_reuseFailAlloc_3744_, 7, v_infoState_3734_);
lean_ctor_set(v_reuseFailAlloc_3744_, 8, v_snapshotTasks_3735_);
v___x_3742_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; 
v___x_3743_ = lean_st_ref_set(v_a_3679_, v___x_3742_);
v_fileName_3706_ = v_fileName_3684_;
v_fileMap_3707_ = v_fileMap_3685_;
v_currRecDepth_3708_ = v_currRecDepth_3687_;
v_ref_3709_ = v_ref_3688_;
v_currNamespace_3710_ = v_currNamespace_3689_;
v_openDecls_3711_ = v_openDecls_3690_;
v_initHeartbeats_3712_ = v_initHeartbeats_3691_;
v_maxHeartbeats_3713_ = v_maxHeartbeats_3692_;
v_quotContext_3714_ = v_quotContext_3693_;
v_currMacroScope_3715_ = v_currMacroScope_3694_;
v_cancelTk_x3f_3716_ = v_cancelTk_x3f_3695_;
v_suppressElabErrors_3717_ = v_suppressElabErrors_3696_;
v_inheritedTraceOptions_3718_ = v_inheritedTraceOptions_3697_;
v___y_3719_ = v_a_3679_;
goto v___jp_3705_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3749_, lean_object* v_info_3750_, lean_object* v_name_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3749_, v_info_3750_, v_name_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
lean_dec(v_a_3755_);
lean_dec_ref(v_a_3754_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3758_, lean_object* v_x_3759_, uint8_t v_isExporting_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
lean_object* v___x_3766_; 
v___x_3766_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3759_, v_isExporting_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3767_, lean_object* v_x_3768_, lean_object* v_isExporting_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v_isExporting_boxed_3775_; lean_object* v_res_3776_; 
v_isExporting_boxed_3775_ = lean_unbox(v_isExporting_3769_);
v_res_3776_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3767_, v_x_3768_, v_isExporting_boxed_3775_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3777_, lean_object* v_x_3778_, uint8_t v_when_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v___x_3785_; 
v___x_3785_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3778_, v_when_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3786_, lean_object* v_x_3787_, lean_object* v_when_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
uint8_t v_when_boxed_3794_; lean_object* v_res_3795_; 
v_when_boxed_3794_ = lean_unbox(v_when_3788_);
v_res_3795_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3786_, v_x_3787_, v_when_boxed_3794_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3796_, lean_object* v_info_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v___x_3803_; lean_object* v_env_3804_; lean_object* v_declName_3805_; lean_object* v_declNames_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3803_ = lean_st_ref_get(v_a_3801_);
v_env_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc_ref(v_env_3804_);
lean_dec(v___x_3803_);
v_declName_3805_ = lean_ctor_get(v_info_3797_, 0);
v_declNames_3806_ = lean_ctor_get(v_info_3797_, 5);
v___x_3807_ = lean_box(0);
v___x_3808_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3805_);
v___x_3809_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3804_, v_declName_3805_, v___x_3808_);
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3811_ = lean_array_get(v___x_3807_, v_declNames_3806_, v___x_3810_);
lean_inc_n(v___x_3809_, 2);
lean_inc(v_declName_3796_);
v___x_3812_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3812_, 0, v_declName_3796_);
lean_closure_set(v___x_3812_, 1, v_info_3797_);
lean_closure_set(v___x_3812_, 2, v___x_3809_);
v___x_3813_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3813_, 0, lean_box(0));
lean_closure_set(v___x_3813_, 1, v_declName_3796_);
lean_closure_set(v___x_3813_, 2, v___x_3812_);
v___x_3814_ = l_Lean_Meta_realizeConst(v___x_3811_, v___x_3809_, v___x_3813_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3821_ == 0)
{
lean_object* v_unused_3822_; 
v_unused_3822_ = lean_ctor_get(v___x_3814_, 0);
lean_dec(v_unused_3822_);
v___x_3816_ = v___x_3814_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_dec(v___x_3814_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3809_);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3809_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec(v___x_3809_);
v_a_3823_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3814_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3814_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3831_, lean_object* v_info_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3831_, v_info_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v___x_3845_; lean_object* v_env_3846_; lean_object* v___x_3847_; lean_object* v_toEnvExtension_3848_; lean_object* v_asyncMode_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; lean_object* v___x_3852_; 
v___x_3845_ = lean_st_ref_get(v_a_3843_);
v_env_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc_ref(v_env_3846_);
lean_dec(v___x_3845_);
v___x_3847_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3848_ = lean_ctor_get(v___x_3847_, 0);
v_asyncMode_3849_ = lean_ctor_get(v_toEnvExtension_3848_, 2);
v___x_3850_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3851_ = 0;
lean_inc(v_declName_3839_);
v___x_3852_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3850_, v___x_3847_, v_env_3846_, v_declName_3839_, v_asyncMode_3849_, v___x_3851_);
if (lean_obj_tag(v___x_3852_) == 1)
{
lean_object* v_val_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3877_; 
v_val_3853_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3855_ = v___x_3852_;
v_isShared_3856_ = v_isSharedCheck_3877_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_val_3853_);
lean_dec(v___x_3852_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3877_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3857_; 
v___x_3857_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3839_, v_val_3853_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3868_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3868_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3868_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v_a_3858_);
v___x_3863_ = v___x_3855_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3865_; 
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3863_);
v___x_3865_ = v___x_3860_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3869_; lean_object* v___x_3871_; uint8_t v_isShared_3872_; uint8_t v_isSharedCheck_3876_; 
lean_del_object(v___x_3855_);
v_a_3869_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3876_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3876_ == 0)
{
v___x_3871_ = v___x_3857_;
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
else
{
lean_inc(v_a_3869_);
lean_dec(v___x_3857_);
v___x_3871_ = lean_box(0);
v_isShared_3872_ = v_isSharedCheck_3876_;
goto v_resetjp_3870_;
}
v_resetjp_3870_:
{
lean_object* v___x_3874_; 
if (v_isShared_3872_ == 0)
{
v___x_3874_ = v___x_3871_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
}
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec(v___x_3852_);
lean_dec(v_declName_3839_);
v___x_3878_ = lean_box(0);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
return v___x_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
lean_dec_ref(v_a_3881_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v___x_3890_; lean_object* v_env_3891_; lean_object* v___x_3892_; lean_object* v_toEnvExtension_3893_; lean_object* v_asyncMode_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; lean_object* v___x_3897_; 
v___x_3890_ = lean_st_ref_get(v_a_3888_);
v_env_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc_ref(v_env_3891_);
lean_dec(v___x_3890_);
v___x_3892_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3893_ = lean_ctor_get(v___x_3892_, 0);
v_asyncMode_3894_ = lean_ctor_get(v_toEnvExtension_3893_, 2);
v___x_3895_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3896_ = 0;
v___x_3897_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3895_, v___x_3892_, v_env_3891_, v_declName_3887_, v_asyncMode_3894_, v___x_3896_);
if (lean_obj_tag(v___x_3897_) == 1)
{
lean_object* v_val_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3907_; 
v_val_3898_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3900_ = v___x_3897_;
v_isShared_3901_ = v_isSharedCheck_3907_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_val_3898_);
lean_dec(v___x_3897_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3907_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_recArgPos_3902_; lean_object* v___x_3904_; 
v_recArgPos_3902_ = lean_ctor_get(v_val_3898_, 4);
lean_inc(v_recArgPos_3902_);
lean_dec(v_val_3898_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 0, v_recArgPos_3902_);
v___x_3904_ = v___x_3900_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_recArgPos_3902_);
v___x_3904_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
return v___x_3905_;
}
}
}
else
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec(v___x_3897_);
v___x_3908_ = lean_box(0);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3910_, v_a_3911_);
lean_dec(v_a_3911_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v___x_3918_; 
lean_dec_ref(v_a_3915_);
v___x_3918_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3914_, v_a_3916_);
lean_dec(v_a_3916_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = lean_get_structural_rec_arg_pos(v_declName_3919_, v_a_3920_, v_a_3921_);
return v_res_3923_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = lean_unsigned_to_nat(2295916746u);
v___x_3982_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3983_ = l_Lean_Name_num___override(v___x_3982_, v___x_3981_);
return v___x_3983_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3986_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3987_ = l_Lean_Name_str___override(v___x_3986_, v___x_3985_);
return v___x_3987_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3990_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3991_ = l_Lean_Name_str___override(v___x_3990_, v___x_3989_);
return v___x_3991_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = lean_unsigned_to_nat(2u);
v___x_3993_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3994_ = l_Lean_Name_num___override(v___x_3993_, v___x_3992_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3997_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3996_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_dec_ref_known(v___x_3997_, 1);
v___x_3998_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4));
v___x_3999_ = 0;
v___x_4000_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_4001_ = l_Lean_registerTraceClass(v___x_3998_, v___x_3999_, v___x_4000_);
return v___x_4001_;
}
else
{
return v___x_3997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_4003_;
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
