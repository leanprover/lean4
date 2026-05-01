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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
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
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Structural"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eqnInfoExt"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 221, 148, 2, 30, 47, 242, 74)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 216, 81, 142, 241, 75, 113, 77)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 185, 97, 74, 150, 8, 57, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Eqns"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 19, 250, 232, 19, 103, 59, 84)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 64, 85, 238, 73, 235, 224, 238)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 241, 197, 13, 174, 23, 186, 239)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(123, 232, 160, 88, 66, 78, 213, 243)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 117, 235, 94, 194, 72, 147, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 146, 13, 135, 45, 158, 59, 107)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 222, 70, 43, 201, 77, 119, 184)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 51, 79, 28, 160, 228, 197, 175)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(130, 14, 83, 143, 58, 41, 180, 194)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 131, 204, 33, 154, 17, 78, 114)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 169, 96, 182, 175, 131, 16, 69)}};
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
lean_dec_ref(v_x_296_);
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
lean_dec_ref(v_x_296_);
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
lean_dec_ref(v_x_296_);
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
lean_dec_ref(v___x_328_);
v___f_330_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__3___redArg___closed__2));
v___x_331_ = 0;
v___x_332_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg(v_a_329_, v___f_330_, v___x_331_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
if (lean_obj_tag(v___x_332_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = lean_array_get_size(v_x_297_);
v___x_335_ = lean_nat_dec_le(v_a_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_a_333_);
lean_dec_ref(v_x_296_);
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
lean_dec_ref(v___x_340_);
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
lean_dec_ref(v_x_296_);
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
lean_dec_ref(v_x_296_);
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
lean_dec_ref(v___x_516_);
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
lean_dec_ref(v___x_683_);
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
lean_dec_ref(v___x_825_);
if (lean_obj_tag(v_val_827_) == 1)
{
uint8_t v_v_828_; 
v_v_828_ = lean_ctor_get_uint8(v_val_827_, 0);
lean_dec_ref(v_val_827_);
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
lean_dec_ref(v___x_943_);
if (lean_obj_tag(v_val_944_) == 3)
{
lean_object* v_v_945_; 
v_v_945_ = lean_ctor_get(v_val_944_, 0);
lean_inc(v_v_945_);
lean_dec_ref(v_val_944_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7(size_t v_sz_949_, size_t v_i_950_, lean_object* v_bs_951_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_950_, v_sz_949_);
if (v___x_952_ == 0)
{
return v_bs_951_;
}
else
{
lean_object* v_v_953_; lean_object* v_msg_954_; lean_object* v___x_955_; lean_object* v_bs_x27_956_; size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v_v_953_ = lean_array_uget_borrowed(v_bs_951_, v_i_950_);
v_msg_954_ = lean_ctor_get(v_v_953_, 1);
lean_inc_ref(v_msg_954_);
v___x_955_ = lean_unsigned_to_nat(0u);
v_bs_x27_956_ = lean_array_uset(v_bs_951_, v_i_950_, v___x_955_);
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_950_, v___x_957_);
v___x_959_ = lean_array_uset(v_bs_x27_956_, v_i_950_, v_msg_954_);
v_i_950_ = v___x_958_;
v_bs_951_ = v___x_959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_961_, lean_object* v_i_962_, lean_object* v_bs_963_){
_start:
{
size_t v_sz_boxed_964_; size_t v_i_boxed_965_; lean_object* v_res_966_; 
v_sz_boxed_964_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v_i_boxed_965_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_res_966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7(v_sz_boxed_964_, v_i_boxed_965_, v_bs_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_oldTraces_967_, lean_object* v_data_968_, lean_object* v_ref_969_, lean_object* v_msg_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_fileName_976_; lean_object* v_fileMap_977_; lean_object* v_options_978_; lean_object* v_currRecDepth_979_; lean_object* v_maxRecDepth_980_; lean_object* v_ref_981_; lean_object* v_currNamespace_982_; lean_object* v_openDecls_983_; lean_object* v_initHeartbeats_984_; lean_object* v_maxHeartbeats_985_; lean_object* v_quotContext_986_; lean_object* v_currMacroScope_987_; uint8_t v_diag_988_; lean_object* v_cancelTk_x3f_989_; uint8_t v_suppressElabErrors_990_; lean_object* v_inheritedTraceOptions_991_; lean_object* v___x_992_; lean_object* v_traceState_993_; lean_object* v_traces_994_; lean_object* v_ref_995_; lean_object* v___x_996_; lean_object* v___x_997_; size_t v_sz_998_; size_t v___x_999_; lean_object* v___x_1000_; lean_object* v_msg_1001_; lean_object* v___x_1002_; lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1040_; 
v_fileName_976_ = lean_ctor_get(v___y_973_, 0);
v_fileMap_977_ = lean_ctor_get(v___y_973_, 1);
v_options_978_ = lean_ctor_get(v___y_973_, 2);
v_currRecDepth_979_ = lean_ctor_get(v___y_973_, 3);
v_maxRecDepth_980_ = lean_ctor_get(v___y_973_, 4);
v_ref_981_ = lean_ctor_get(v___y_973_, 5);
v_currNamespace_982_ = lean_ctor_get(v___y_973_, 6);
v_openDecls_983_ = lean_ctor_get(v___y_973_, 7);
v_initHeartbeats_984_ = lean_ctor_get(v___y_973_, 8);
v_maxHeartbeats_985_ = lean_ctor_get(v___y_973_, 9);
v_quotContext_986_ = lean_ctor_get(v___y_973_, 10);
v_currMacroScope_987_ = lean_ctor_get(v___y_973_, 11);
v_diag_988_ = lean_ctor_get_uint8(v___y_973_, sizeof(void*)*14);
v_cancelTk_x3f_989_ = lean_ctor_get(v___y_973_, 12);
v_suppressElabErrors_990_ = lean_ctor_get_uint8(v___y_973_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_991_ = lean_ctor_get(v___y_973_, 13);
v___x_992_ = lean_st_ref_get(v___y_974_);
v_traceState_993_ = lean_ctor_get(v___x_992_, 4);
lean_inc_ref(v_traceState_993_);
lean_dec(v___x_992_);
v_traces_994_ = lean_ctor_get(v_traceState_993_, 0);
lean_inc_ref(v_traces_994_);
lean_dec_ref(v_traceState_993_);
v_ref_995_ = l_Lean_replaceRef(v_ref_969_, v_ref_981_);
lean_inc_ref(v_inheritedTraceOptions_991_);
lean_inc(v_cancelTk_x3f_989_);
lean_inc(v_currMacroScope_987_);
lean_inc(v_quotContext_986_);
lean_inc(v_maxHeartbeats_985_);
lean_inc(v_initHeartbeats_984_);
lean_inc(v_openDecls_983_);
lean_inc(v_currNamespace_982_);
lean_inc(v_maxRecDepth_980_);
lean_inc(v_currRecDepth_979_);
lean_inc_ref(v_options_978_);
lean_inc_ref(v_fileMap_977_);
lean_inc_ref(v_fileName_976_);
v___x_996_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_996_, 0, v_fileName_976_);
lean_ctor_set(v___x_996_, 1, v_fileMap_977_);
lean_ctor_set(v___x_996_, 2, v_options_978_);
lean_ctor_set(v___x_996_, 3, v_currRecDepth_979_);
lean_ctor_set(v___x_996_, 4, v_maxRecDepth_980_);
lean_ctor_set(v___x_996_, 5, v_ref_995_);
lean_ctor_set(v___x_996_, 6, v_currNamespace_982_);
lean_ctor_set(v___x_996_, 7, v_openDecls_983_);
lean_ctor_set(v___x_996_, 8, v_initHeartbeats_984_);
lean_ctor_set(v___x_996_, 9, v_maxHeartbeats_985_);
lean_ctor_set(v___x_996_, 10, v_quotContext_986_);
lean_ctor_set(v___x_996_, 11, v_currMacroScope_987_);
lean_ctor_set(v___x_996_, 12, v_cancelTk_x3f_989_);
lean_ctor_set(v___x_996_, 13, v_inheritedTraceOptions_991_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*14, v_diag_988_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*14 + 1, v_suppressElabErrors_990_);
v___x_997_ = l_Lean_PersistentArray_toArray___redArg(v_traces_994_);
lean_dec_ref(v_traces_994_);
v_sz_998_ = lean_array_size(v___x_997_);
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7(v_sz_998_, v___x_999_, v___x_997_);
v_msg_1001_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1001_, 0, v_data_968_);
lean_ctor_set(v_msg_1001_, 1, v_msg_970_);
lean_ctor_set(v_msg_1001_, 2, v___x_1000_);
v___x_1002_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_1001_, v___y_971_, v___y_972_, v___x_996_, v___y_974_);
lean_dec_ref(v___x_996_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1040_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1040_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v_traceState_1008_; lean_object* v_env_1009_; lean_object* v_nextMacroScope_1010_; lean_object* v_ngen_1011_; lean_object* v_auxDeclNGen_1012_; lean_object* v_cache_1013_; lean_object* v_messages_1014_; lean_object* v_infoState_1015_; lean_object* v_snapshotTasks_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1039_; 
v___x_1007_ = lean_st_ref_take(v___y_974_);
v_traceState_1008_ = lean_ctor_get(v___x_1007_, 4);
v_env_1009_ = lean_ctor_get(v___x_1007_, 0);
v_nextMacroScope_1010_ = lean_ctor_get(v___x_1007_, 1);
v_ngen_1011_ = lean_ctor_get(v___x_1007_, 2);
v_auxDeclNGen_1012_ = lean_ctor_get(v___x_1007_, 3);
v_cache_1013_ = lean_ctor_get(v___x_1007_, 5);
v_messages_1014_ = lean_ctor_get(v___x_1007_, 6);
v_infoState_1015_ = lean_ctor_get(v___x_1007_, 7);
v_snapshotTasks_1016_ = lean_ctor_get(v___x_1007_, 8);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1018_ = v___x_1007_;
v_isShared_1019_ = v_isSharedCheck_1039_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_snapshotTasks_1016_);
lean_inc(v_infoState_1015_);
lean_inc(v_messages_1014_);
lean_inc(v_cache_1013_);
lean_inc(v_traceState_1008_);
lean_inc(v_auxDeclNGen_1012_);
lean_inc(v_ngen_1011_);
lean_inc(v_nextMacroScope_1010_);
lean_inc(v_env_1009_);
lean_dec(v___x_1007_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1039_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
uint64_t v_tid_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1037_; 
v_tid_1020_ = lean_ctor_get_uint64(v_traceState_1008_, sizeof(void*)*1);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_traceState_1008_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_traceState_1008_, 0);
lean_dec(v_unused_1038_);
v___x_1022_ = v_traceState_1008_;
v_isShared_1023_ = v_isSharedCheck_1037_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v_traceState_1008_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1037_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v_ref_969_);
lean_ctor_set(v___x_1024_, 1, v_a_1003_);
v___x_1025_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_967_, v___x_1024_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1025_);
v___x_1027_ = v___x_1022_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1025_);
lean_ctor_set_uint64(v_reuseFailAlloc_1036_, sizeof(void*)*1, v_tid_1020_);
v___x_1027_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 4, v___x_1027_);
v___x_1029_ = v___x_1018_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_env_1009_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v_nextMacroScope_1010_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_ngen_1011_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v_auxDeclNGen_1012_);
lean_ctor_set(v_reuseFailAlloc_1035_, 4, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1035_, 5, v_cache_1013_);
lean_ctor_set(v_reuseFailAlloc_1035_, 6, v_messages_1014_);
lean_ctor_set(v_reuseFailAlloc_1035_, 7, v_infoState_1015_);
lean_ctor_set(v_reuseFailAlloc_1035_, 8, v_snapshotTasks_1016_);
v___x_1029_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1030_ = lean_st_ref_set(v___y_974_, v___x_1029_);
v___x_1031_ = lean_box(0);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1031_);
v___x_1033_ = v___x_1005_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_oldTraces_1041_, lean_object* v_data_1042_, lean_object* v_ref_1043_, lean_object* v_msg_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_oldTraces_1041_, v_data_1042_, v_ref_1043_, v_msg_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
v_a_1053_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v_x_1051_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v_x_1051_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 1);
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_a_1061_ = lean_ctor_get(v_x_1051_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_1051_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v_x_1051_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v_x_1051_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set_tag(v___x_1063_, 0);
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg___boxed(lean_object* v_x_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_x_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object* v_e_1072_){
_start:
{
if (lean_obj_tag(v_e_1072_) == 0)
{
uint8_t v___x_1073_; 
v___x_1073_ = 2;
return v___x_1073_;
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = 0;
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object* v_e_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_e_1075_);
lean_dec_ref(v_e_1075_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1084_; double v___x_1085_; 
v___x_1084_ = lean_unsigned_to_nat(1000u);
v___x_1085_ = lean_float_of_nat(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_cls_1086_, uint8_t v_collapsed_1087_, lean_object* v_tag_1088_, lean_object* v_opts_1089_, uint8_t v_clsEnabled_1090_, lean_object* v_oldTraces_1091_, lean_object* v_msg_1092_, lean_object* v_resStartStop_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1190_; 
v_fst_1099_ = lean_ctor_get(v_resStartStop_1093_, 0);
v_snd_1100_ = lean_ctor_get(v_resStartStop_1093_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_resStartStop_1093_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1102_ = v_resStartStop_1093_;
v_isShared_1103_ = v_isSharedCheck_1190_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_snd_1100_);
lean_inc(v_fst_1099_);
lean_dec(v_resStartStop_1093_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1190_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v_data_1107_; lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1189_; 
v_fst_1110_ = lean_ctor_get(v_snd_1100_, 0);
v_snd_1111_ = lean_ctor_get(v_snd_1100_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_snd_1100_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1113_ = v_snd_1100_;
v_isShared_1114_ = v_isSharedCheck_1189_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1110_);
lean_dec(v_snd_1100_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1189_;
goto v_resetjp_1112_;
}
v___jp_1104_:
{
lean_object* v___x_1108_; 
lean_inc(v___y_1105_);
v___x_1108_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_oldTraces_1091_, v_data_1107_, v___y_1105_, v___y_1106_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v___x_1109_; 
lean_dec_ref(v___x_1108_);
v___x_1109_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_1099_);
return v___x_1109_;
}
else
{
lean_dec(v_fst_1099_);
return v___x_1108_;
}
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v___y_1118_; lean_object* v_a_1119_; uint8_t v___y_1143_; double v___y_1174_; 
v___x_1115_ = l_Lean_trace_profiler;
v___x_1116_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1089_, v___x_1115_);
if (v___x_1116_ == 0)
{
v___y_1143_ = v___x_1116_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1179_; uint8_t v___x_1180_; 
v___x_1179_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1180_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1089_, v___x_1179_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; double v___x_1183_; double v___x_1184_; double v___x_1185_; 
v___x_1181_ = l_Lean_trace_profiler_threshold;
v___x_1182_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1089_, v___x_1181_);
v___x_1183_ = lean_float_of_nat(v___x_1182_);
v___x_1184_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4);
v___x_1185_ = lean_float_div(v___x_1183_, v___x_1184_);
v___y_1174_ = v___x_1185_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; double v___x_1188_; 
v___x_1186_ = l_Lean_trace_profiler_threshold;
v___x_1187_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1089_, v___x_1186_);
v___x_1188_ = lean_float_of_nat(v___x_1187_);
v___y_1174_ = v___x_1188_;
goto v___jp_1173_;
}
}
v___jp_1117_:
{
uint8_t v_result_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v_result_1120_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_fst_1099_);
v___x_1121_ = l_Lean_TraceResult_toEmoji(v_result_1120_);
v___x_1122_ = l_Lean_stringToMessageData(v___x_1121_);
v___x_1123_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 7);
lean_ctor_set(v___x_1113_, 1, v___x_1123_);
lean_ctor_set(v___x_1113_, 0, v___x_1122_);
v___x_1125_ = v___x_1113_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v_m_1127_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 7);
lean_ctor_set(v___x_1102_, 1, v_a_1119_);
lean_ctor_set(v___x_1102_, 0, v___x_1125_);
v_m_1127_ = v___x_1102_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_a_1119_);
v_m_1127_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; double v___x_1130_; lean_object* v_data_1131_; 
v___x_1128_ = lean_box(v_result_1120_);
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
v___x_1130_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_1088_);
lean_inc_ref(v___x_1129_);
lean_inc(v_cls_1086_);
v_data_1131_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1131_, 0, v_cls_1086_);
lean_ctor_set(v_data_1131_, 1, v___x_1129_);
lean_ctor_set(v_data_1131_, 2, v_tag_1088_);
lean_ctor_set_float(v_data_1131_, sizeof(void*)*3, v___x_1130_);
lean_ctor_set_float(v_data_1131_, sizeof(void*)*3 + 8, v___x_1130_);
lean_ctor_set_uint8(v_data_1131_, sizeof(void*)*3 + 16, v_collapsed_1087_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v___x_1129_);
lean_dec(v_snd_1111_);
lean_dec(v_fst_1110_);
lean_dec_ref(v_tag_1088_);
lean_dec(v_cls_1086_);
v___y_1105_ = v___y_1118_;
v___y_1106_ = v_m_1127_;
v_data_1107_ = v_data_1131_;
goto v___jp_1104_;
}
else
{
lean_object* v_data_1132_; double v___x_1133_; double v___x_1134_; 
lean_dec_ref(v_data_1131_);
v_data_1132_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1132_, 0, v_cls_1086_);
lean_ctor_set(v_data_1132_, 1, v___x_1129_);
lean_ctor_set(v_data_1132_, 2, v_tag_1088_);
v___x_1133_ = lean_unbox_float(v_fst_1110_);
lean_dec(v_fst_1110_);
lean_ctor_set_float(v_data_1132_, sizeof(void*)*3, v___x_1133_);
v___x_1134_ = lean_unbox_float(v_snd_1111_);
lean_dec(v_snd_1111_);
lean_ctor_set_float(v_data_1132_, sizeof(void*)*3 + 8, v___x_1134_);
lean_ctor_set_uint8(v_data_1132_, sizeof(void*)*3 + 16, v_collapsed_1087_);
v___y_1105_ = v___y_1118_;
v___y_1106_ = v_m_1127_;
v_data_1107_ = v_data_1132_;
goto v___jp_1104_;
}
}
}
}
v___jp_1137_:
{
lean_object* v_ref_1138_; lean_object* v___x_1139_; 
v_ref_1138_ = lean_ctor_get(v___y_1096_, 5);
lean_inc(v___y_1097_);
lean_inc_ref(v___y_1096_);
lean_inc(v___y_1095_);
lean_inc_ref(v___y_1094_);
lean_inc(v_fst_1099_);
v___x_1139_ = lean_apply_6(v_msg_1092_, v_fst_1099_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, lean_box(0));
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v___x_1139_);
v___y_1118_ = v_ref_1138_;
v_a_1119_ = v_a_1140_;
goto v___jp_1117_;
}
else
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_1139_);
v___x_1141_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3);
v___y_1118_ = v_ref_1138_;
v_a_1119_ = v___x_1141_;
goto v___jp_1117_;
}
}
v___jp_1142_:
{
if (v_clsEnabled_1090_ == 0)
{
if (v___y_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v_traceState_1145_; lean_object* v_env_1146_; lean_object* v_nextMacroScope_1147_; lean_object* v_ngen_1148_; lean_object* v_auxDeclNGen_1149_; lean_object* v_cache_1150_; lean_object* v_messages_1151_; lean_object* v_infoState_1152_; lean_object* v_snapshotTasks_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1172_; 
lean_del_object(v___x_1113_);
lean_dec(v_snd_1111_);
lean_dec(v_fst_1110_);
lean_del_object(v___x_1102_);
lean_dec_ref(v_msg_1092_);
lean_dec_ref(v_tag_1088_);
lean_dec(v_cls_1086_);
v___x_1144_ = lean_st_ref_take(v___y_1097_);
v_traceState_1145_ = lean_ctor_get(v___x_1144_, 4);
v_env_1146_ = lean_ctor_get(v___x_1144_, 0);
v_nextMacroScope_1147_ = lean_ctor_get(v___x_1144_, 1);
v_ngen_1148_ = lean_ctor_get(v___x_1144_, 2);
v_auxDeclNGen_1149_ = lean_ctor_get(v___x_1144_, 3);
v_cache_1150_ = lean_ctor_get(v___x_1144_, 5);
v_messages_1151_ = lean_ctor_get(v___x_1144_, 6);
v_infoState_1152_ = lean_ctor_get(v___x_1144_, 7);
v_snapshotTasks_1153_ = lean_ctor_get(v___x_1144_, 8);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1155_ = v___x_1144_;
v_isShared_1156_ = v_isSharedCheck_1172_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_snapshotTasks_1153_);
lean_inc(v_infoState_1152_);
lean_inc(v_messages_1151_);
lean_inc(v_cache_1150_);
lean_inc(v_traceState_1145_);
lean_inc(v_auxDeclNGen_1149_);
lean_inc(v_ngen_1148_);
lean_inc(v_nextMacroScope_1147_);
lean_inc(v_env_1146_);
lean_dec(v___x_1144_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1172_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint64_t v_tid_1157_; lean_object* v_traces_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1171_; 
v_tid_1157_ = lean_ctor_get_uint64(v_traceState_1145_, sizeof(void*)*1);
v_traces_1158_ = lean_ctor_get(v_traceState_1145_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_traceState_1145_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1160_ = v_traceState_1145_;
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_traces_1158_);
lean_dec(v_traceState_1145_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1091_, v_traces_1158_);
lean_dec_ref(v_traces_1158_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1162_);
lean_ctor_set_uint64(v_reuseFailAlloc_1170_, sizeof(void*)*1, v_tid_1157_);
v___x_1164_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 4, v___x_1164_);
v___x_1166_ = v___x_1155_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_env_1146_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_nextMacroScope_1147_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_ngen_1148_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_auxDeclNGen_1149_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1169_, 5, v_cache_1150_);
lean_ctor_set(v_reuseFailAlloc_1169_, 6, v_messages_1151_);
lean_ctor_set(v_reuseFailAlloc_1169_, 7, v_infoState_1152_);
lean_ctor_set(v_reuseFailAlloc_1169_, 8, v_snapshotTasks_1153_);
v___x_1166_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_st_ref_set(v___y_1097_, v___x_1166_);
v___x_1168_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_1099_);
return v___x_1168_;
}
}
}
}
}
else
{
goto v___jp_1137_;
}
}
else
{
goto v___jp_1137_;
}
}
v___jp_1173_:
{
double v___x_1175_; double v___x_1176_; double v___x_1177_; uint8_t v___x_1178_; 
v___x_1175_ = lean_unbox_float(v_snd_1111_);
v___x_1176_ = lean_unbox_float(v_fst_1110_);
v___x_1177_ = lean_float_sub(v___x_1175_, v___x_1176_);
v___x_1178_ = lean_float_decLt(v___y_1174_, v___x_1177_);
v___y_1143_ = v___x_1178_;
goto v___jp_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_cls_1191_, lean_object* v_collapsed_1192_, lean_object* v_tag_1193_, lean_object* v_opts_1194_, lean_object* v_clsEnabled_1195_, lean_object* v_oldTraces_1196_, lean_object* v_msg_1197_, lean_object* v_resStartStop_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v_collapsed_boxed_1204_; uint8_t v_clsEnabled_boxed_1205_; lean_object* v_res_1206_; 
v_collapsed_boxed_1204_ = lean_unbox(v_collapsed_1192_);
v_clsEnabled_boxed_1205_ = lean_unbox(v_clsEnabled_1195_);
v_res_1206_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1191_, v_collapsed_boxed_1204_, v_tag_1193_, v_opts_1194_, v_clsEnabled_boxed_1205_, v_oldTraces_1196_, v_msg_1197_, v_resStartStop_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec_ref(v_opts_1194_);
return v_res_1206_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1209_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1(void){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_unsigned_to_nat(16u);
v___x_1214_ = lean_mk_array(v___x_1213_, v___x_1212_);
return v___x_1214_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2(void){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1215_);
return v___x_1217_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1219_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1220_ = 1;
v___x_1221_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1218_);
lean_ctor_set_uint8(v___x_1221_, sizeof(void*)*2, v___x_1220_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1222_ = lean_unsigned_to_nat(32u);
v___x_1223_ = lean_mk_empty_array_with_capacity(v___x_1222_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
size_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1225_ = ((size_t)5ULL);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = lean_unsigned_to_nat(32u);
v___x_1228_ = lean_mk_empty_array_with_capacity(v___x_1227_);
v___x_1229_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7);
v___x_1230_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
lean_ctor_set(v___x_1230_, 1, v___x_1228_);
lean_ctor_set(v___x_1230_, 2, v___x_1226_);
lean_ctor_set(v___x_1230_, 3, v___x_1226_);
lean_ctor_set_usize(v___x_1230_, 4, v___x_1225_);
return v___x_1230_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1232_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1233_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
lean_ctor_set(v___x_1233_, 2, v___x_1232_);
lean_ctor_set(v___x_1233_, 3, v___x_1231_);
return v___x_1233_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1234_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9);
v___x_1238_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v___x_1238_);
lean_ctor_set(v___x_1239_, 1, v___x_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_declName_1240_, lean_object* v_as_1241_, size_t v_i_1242_, size_t v_stop_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v___x_1250_; 
v___x_1250_ = lean_usize_dec_eq(v_i_1242_, v_stop_1243_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = lean_array_uget_borrowed(v_as_1241_, v_i_1242_);
lean_inc(v___x_1251_);
lean_inc(v_declName_1240_);
v___x_1252_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1240_, v___x_1251_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; size_t v___x_1254_; size_t v___x_1255_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_a_1253_);
lean_dec_ref(v___x_1252_);
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_add(v_i_1242_, v___x_1254_);
v_i_1242_ = v___x_1255_;
v_b_1244_ = v_a_1253_;
goto _start;
}
else
{
lean_dec(v_declName_1240_);
return v___x_1252_;
}
}
else
{
lean_object* v___x_1257_; 
lean_dec(v_declName_1240_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_b_1244_);
return v___x_1257_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v_cls_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_cls_1273_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1274_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_1275_ = l_Lean_Name_append(v___x_1274_, v_cls_1273_);
return v___x_1275_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1276_; double v___x_1277_; 
v___x_1276_ = lean_unsigned_to_nat(1000000000u);
v___x_1277_ = lean_float_of_nat(v___x_1276_);
return v___x_1277_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1293_, lean_object* v___x_1294_, lean_object* v_declName_1295_, lean_object* v_____r_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1302_ = lean_array_get_size(v_val_1293_);
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_nat_dec_lt(v___x_1294_, v___x_1302_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; 
lean_dec(v_declName_1295_);
v___x_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
return v___x_1305_;
}
else
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_nat_dec_le(v___x_1302_, v___x_1302_);
if (v___x_1306_ == 0)
{
if (v___x_1304_ == 0)
{
lean_object* v___x_1307_; 
lean_dec(v_declName_1295_);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1303_);
return v___x_1307_;
}
else
{
size_t v___x_1308_; size_t v___x_1309_; lean_object* v___x_1310_; 
v___x_1308_ = ((size_t)0ULL);
v___x_1309_ = lean_usize_of_nat(v___x_1302_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1295_, v_val_1293_, v___x_1308_, v___x_1309_, v___x_1303_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1310_;
}
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1302_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1295_, v_val_1293_, v___x_1311_, v___x_1312_, v___x_1303_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
return v___x_1313_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1316_ = l_Lean_stringToMessageData(v___x_1315_);
return v___x_1316_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1319_ = l_Lean_stringToMessageData(v___x_1318_);
return v___x_1319_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1322_ = l_Lean_stringToMessageData(v___x_1321_);
return v___x_1322_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1325_ = l_Lean_stringToMessageData(v___x_1324_);
return v___x_1325_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1328_ = l_Lean_stringToMessageData(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1329_, lean_object* v_mvarId_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_options_1342_; uint8_t v_hasTrace_1343_; 
v_options_1342_ = lean_ctor_get(v_a_1333_, 2);
v_hasTrace_1343_ = lean_ctor_get_uint8(v_options_1342_, sizeof(void*)*1);
if (v_hasTrace_1343_ == 0)
{
lean_object* v___x_1344_; 
lean_inc(v_mvarId_1330_);
v___x_1344_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1516_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1347_ = v___x_1344_;
v_isShared_1348_ = v_isSharedCheck_1516_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1344_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1516_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v___x_1349_; 
v___x_1349_ = lean_unbox(v_a_1345_);
lean_dec(v_a_1345_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_del_object(v___x_1347_);
lean_inc(v_mvarId_1330_);
v___x_1350_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1503_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1353_ = v___x_1350_;
v_isShared_1354_ = v_isSharedCheck_1503_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1350_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1503_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_unbox(v_a_1351_);
lean_dec(v_a_1351_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_del_object(v___x_1353_);
lean_inc(v_mvarId_1330_);
v___x_1356_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
if (lean_obj_tag(v_a_1357_) == 1)
{
lean_object* v_val_1358_; 
lean_dec(v_mvarId_1330_);
v_val_1358_ = lean_ctor_get(v_a_1357_, 0);
lean_inc(v_val_1358_);
lean_dec_ref(v_a_1357_);
v_mvarId_1330_ = v_val_1358_;
goto _start;
}
else
{
lean_object* v___x_1360_; 
lean_dec(v_a_1357_);
lean_inc(v_mvarId_1330_);
v___x_1360_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
if (lean_obj_tag(v_a_1361_) == 1)
{
lean_object* v_val_1362_; 
lean_dec(v_mvarId_1330_);
v_val_1362_ = lean_ctor_get(v_a_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v_a_1361_);
v_mvarId_1330_ = v_val_1362_;
goto _start;
}
else
{
uint8_t v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v_a_1361_);
v___x_1364_ = 1;
lean_inc(v_mvarId_1330_);
v___x_1365_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1330_, v___x_1364_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_a_1366_);
lean_dec_ref(v___x_1365_);
if (lean_obj_tag(v_a_1366_) == 1)
{
lean_object* v_val_1367_; 
lean_dec(v_mvarId_1330_);
v_val_1367_ = lean_ctor_get(v_a_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref(v_a_1366_);
v_mvarId_1330_ = v_val_1367_;
goto _start;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec(v_a_1366_);
v___x_1369_ = lean_unsigned_to_nat(100000u);
v___x_1370_ = lean_unsigned_to_nat(2u);
v___x_1371_ = 0;
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1373_, 0, v___x_1369_);
lean_ctor_set(v___x_1373_, 1, v___x_1370_);
lean_ctor_set(v___x_1373_, 2, v___x_1372_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 1, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 2, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 3, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 4, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 5, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 6, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 7, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 8, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 9, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 10, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 11, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 12, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 13, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 14, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 15, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 16, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 17, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 18, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 19, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 20, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 21, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 22, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 23, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 24, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 25, v___x_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 26, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 27, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 28, v_hasTrace_1343_);
v___x_1374_ = lean_unsigned_to_nat(0u);
v___x_1375_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1376_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1377_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1373_, v___x_1375_, v___x_1376_, v_a_1331_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref(v___x_1377_);
v___x_1379_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1330_);
v___x_1380_ = l_Lean_Meta_simpTargetStar(v_mvarId_1330_, v_a_1378_, v___x_1375_, v___x_1372_, v___x_1379_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1458_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1458_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1458_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_fst_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1456_; 
v_fst_1385_ = lean_ctor_get(v_a_1381_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_a_1381_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_a_1381_, 1);
lean_dec(v_unused_1457_);
v___x_1387_ = v_a_1381_;
v_isShared_1388_ = v_isSharedCheck_1456_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_fst_1385_);
lean_dec(v_a_1381_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1456_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
switch(lean_obj_tag(v_fst_1385_))
{
case 0:
{
lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v___x_1389_ = lean_box(0);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1389_);
v___x_1391_ = v___x_1383_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
case 1:
{
lean_object* v___x_1393_; 
lean_del_object(v___x_1383_);
lean_inc(v_declName_1329_);
lean_inc(v_mvarId_1330_);
v___x_1393_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1330_, v_declName_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
if (lean_obj_tag(v_a_1394_) == 1)
{
lean_object* v_val_1395_; 
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1330_);
v_val_1395_ = lean_ctor_get(v_a_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref(v_a_1394_);
v_mvarId_1330_ = v_val_1395_;
goto _start;
}
else
{
lean_object* v___x_1397_; 
lean_dec(v_a_1394_);
lean_inc(v_mvarId_1330_);
v___x_1397_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1437_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1437_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1437_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; uint8_t v___x_1405_; 
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1330_);
v_val_1402_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1402_);
lean_dec_ref(v_a_1398_);
v___x_1403_ = lean_array_get_size(v_val_1402_);
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_nat_dec_lt(v___x_1374_, v___x_1403_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_val_1402_);
lean_dec(v_declName_1329_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1404_);
v___x_1407_ = v___x_1400_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1404_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_nat_dec_le(v___x_1403_, v___x_1403_);
if (v___x_1409_ == 0)
{
if (v___x_1405_ == 0)
{
lean_object* v___x_1411_; 
lean_dec(v_val_1402_);
lean_dec(v_declName_1329_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1404_);
v___x_1411_ = v___x_1400_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1404_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
else
{
size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
lean_del_object(v___x_1400_);
v___x_1413_ = ((size_t)0ULL);
v___x_1414_ = lean_usize_of_nat(v___x_1403_);
v___x_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1329_, v_val_1402_, v___x_1413_, v___x_1414_, v___x_1404_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_val_1402_);
return v___x_1415_;
}
}
else
{
size_t v___x_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
lean_del_object(v___x_1400_);
v___x_1416_ = ((size_t)0ULL);
v___x_1417_ = lean_usize_of_nat(v___x_1403_);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1329_, v_val_1402_, v___x_1416_, v___x_1417_, v___x_1404_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_val_1402_);
return v___x_1418_;
}
}
}
else
{
lean_object* v___x_1419_; 
lean_del_object(v___x_1400_);
lean_dec(v_a_1398_);
lean_inc(v_mvarId_1330_);
v___x_1419_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1330_, v___x_1364_, v___x_1364_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1419_);
if (lean_obj_tag(v_a_1420_) == 1)
{
lean_object* v_val_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1330_);
v_val_1421_ = lean_ctor_get(v_a_1420_, 0);
lean_inc(v_val_1421_);
lean_dec_ref(v_a_1420_);
v___x_1422_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1329_, v_val_1421_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1422_;
}
else
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
lean_dec(v_a_1420_);
lean_dec(v_declName_1329_);
v___x_1423_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_mvarId_1330_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set_tag(v___x_1387_, 7);
lean_ctor_set(v___x_1387_, 1, v___x_1424_);
lean_ctor_set(v___x_1387_, 0, v___x_1423_);
v___x_1426_ = v___x_1387_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1426_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1427_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1429_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1419_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1419_);
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
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1438_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1397_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1397_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1446_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1393_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1393_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
default: 
{
lean_object* v_mvarId_1454_; 
lean_del_object(v___x_1387_);
lean_del_object(v___x_1383_);
lean_dec(v_mvarId_1330_);
v_mvarId_1454_ = lean_ctor_get(v_fst_1385_, 0);
lean_inc(v_mvarId_1454_);
lean_dec_ref(v_fst_1385_);
v_mvarId_1330_ = v_mvarId_1454_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1459_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1380_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1380_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1467_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1377_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1377_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1475_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1365_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1365_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1483_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1360_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1360_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1491_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1356_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1356_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v___x_1499_ = lean_box(0);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1499_);
v___x_1501_ = v___x_1353_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1504_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1350_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1350_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v___x_1512_ = lean_box(0);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 0, v___x_1512_);
v___x_1514_ = v___x_1347_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1517_ = lean_ctor_get(v___x_1344_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1344_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v___x_1344_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1344_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1525_; lean_object* v___f_1526_; lean_object* v_cls_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v_a_1534_; lean_object* v___y_1544_; lean_object* v___y_1545_; lean_object* v_a_1546_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v_a_1551_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1560_; lean_object* v___y_1561_; lean_object* v_a_1562_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v_a_1577_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v_a_1582_; lean_object* v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; 
v_inheritedTraceOptions_1525_ = lean_ctor_get(v_a_1333_, 13);
lean_inc(v_mvarId_1330_);
v___f_1526_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1526_, 0, v_mvarId_1330_);
v_cls_1527_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1528_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1529_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1525_, v_options_1342_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = l_Lean_trace_profiler;
v___x_1857_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1342_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref(v___f_1526_);
lean_inc(v_mvarId_1330_);
v___x_1858_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; uint8_t v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = lean_unbox(v_a_1859_);
lean_dec(v_a_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_inc(v_mvarId_1330_);
v___x_1861_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; uint8_t v___x_1863_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = lean_unbox(v_a_1862_);
lean_dec(v_a_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_inc(v_mvarId_1330_);
v___x_1864_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
if (lean_obj_tag(v_a_1865_) == 1)
{
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1866_; 
v_val_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref(v_a_1865_);
v_mvarId_1330_ = v_val_1866_;
goto _start;
}
else
{
lean_object* v_val_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_val_1868_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_val_1868_);
lean_dec_ref(v_a_1865_);
v___x_1869_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1870_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1869_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_dec_ref(v___x_1870_);
v_mvarId_1330_ = v_val_1868_;
goto _start;
}
else
{
lean_dec(v_val_1868_);
lean_dec(v_declName_1329_);
return v___x_1870_;
}
}
}
else
{
lean_object* v___x_1872_; 
lean_dec(v_a_1865_);
lean_inc(v_mvarId_1330_);
v___x_1872_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
if (lean_obj_tag(v_a_1873_) == 1)
{
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1874_; 
v_val_1874_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref(v_a_1873_);
v_mvarId_1330_ = v_val_1874_;
goto _start;
}
else
{
lean_object* v_val_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v_val_1876_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_val_1876_);
lean_dec_ref(v_a_1873_);
v___x_1877_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1878_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1877_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_dec_ref(v___x_1878_);
v_mvarId_1330_ = v_val_1876_;
goto _start;
}
else
{
lean_dec(v_val_1876_);
lean_dec(v_declName_1329_);
return v___x_1878_;
}
}
}
else
{
lean_object* v___x_1880_; 
lean_dec(v_a_1873_);
lean_inc(v_mvarId_1330_);
v___x_1880_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1330_, v_hasTrace_1343_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
if (lean_obj_tag(v_a_1881_) == 1)
{
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1882_; 
v_val_1882_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_val_1882_);
lean_dec_ref(v_a_1881_);
v_mvarId_1330_ = v_val_1882_;
goto _start;
}
else
{
lean_object* v_val_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_val_1884_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_val_1884_);
lean_dec_ref(v_a_1881_);
v___x_1885_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1886_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1885_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_dec_ref(v___x_1886_);
v_mvarId_1330_ = v_val_1884_;
goto _start;
}
else
{
lean_dec(v_val_1884_);
lean_dec(v_declName_1329_);
return v___x_1886_;
}
}
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
lean_dec(v_a_1881_);
v___x_1888_ = lean_unsigned_to_nat(100000u);
v___x_1889_ = lean_unsigned_to_nat(2u);
v___x_1890_ = 0;
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1892_, 0, v___x_1888_);
lean_ctor_set(v___x_1892_, 1, v___x_1889_);
lean_ctor_set(v___x_1892_, 2, v___x_1891_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 1, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 2, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 3, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 4, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 5, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 6, v___x_1890_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 7, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 8, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 9, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 10, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 11, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 12, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 13, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 14, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 15, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 16, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 17, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 18, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 19, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 20, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 21, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 22, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 23, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 24, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 25, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 26, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 27, v___x_1857_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 28, v___x_1857_);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1895_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1896_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1897_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
lean_ctor_set_uint8(v___x_1897_, sizeof(void*)*2, v_hasTrace_1343_);
v___x_1898_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1892_, v___x_1894_, v___x_1897_, v_a_1331_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1330_);
v___x_1901_ = l_Lean_Meta_simpTargetStar(v_mvarId_1330_, v_a_1899_, v___x_1894_, v___x_1891_, v___x_1900_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_2000_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_2000_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_2000_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v_fst_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1998_; 
v_fst_1906_ = lean_ctor_get(v_a_1902_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_a_1902_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v_a_1902_, 1);
lean_dec(v_unused_1999_);
v___x_1908_ = v_a_1902_;
v_isShared_1909_ = v_isSharedCheck_1998_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_fst_1906_);
lean_dec(v_a_1902_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1998_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
switch(lean_obj_tag(v_fst_1906_))
{
case 0:
{
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1910_ = lean_box(0);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1910_);
v___x_1912_ = v___x_1904_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_del_object(v___x_1904_);
v___x_1914_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1915_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1914_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1915_;
}
}
case 1:
{
lean_object* v___x_1916_; 
lean_del_object(v___x_1904_);
lean_inc(v_declName_1329_);
lean_inc(v_mvarId_1330_);
v___x_1916_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1330_, v_declName_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref(v___x_1916_);
if (lean_obj_tag(v_a_1917_) == 1)
{
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1918_; 
v_val_1918_ = lean_ctor_get(v_a_1917_, 0);
lean_inc(v_val_1918_);
lean_dec_ref(v_a_1917_);
v_mvarId_1330_ = v_val_1918_;
goto _start;
}
else
{
lean_object* v_val_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_val_1920_ = lean_ctor_get(v_a_1917_, 0);
lean_inc(v_val_1920_);
lean_dec_ref(v_a_1917_);
v___x_1921_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1922_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1921_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_dec_ref(v___x_1922_);
v_mvarId_1330_ = v_val_1920_;
goto _start;
}
else
{
lean_dec(v_val_1920_);
lean_dec(v_declName_1329_);
return v___x_1922_;
}
}
}
else
{
lean_object* v___x_1924_; 
lean_dec(v_a_1917_);
lean_inc(v_mvarId_1330_);
v___x_1924_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1975_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1975_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1975_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
if (lean_obj_tag(v_a_1925_) == 1)
{
lean_object* v_val_1929_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; 
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1330_);
v_val_1929_ = lean_ctor_get(v_a_1925_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v_a_1925_);
if (v___x_1530_ == 0)
{
v___y_1931_ = v_a_1331_;
v___y_1932_ = v_a_1332_;
v___y_1933_ = v_a_1333_;
v___y_1934_ = v_a_1334_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1952_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1951_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_dec_ref(v___x_1952_);
v___y_1931_ = v_a_1331_;
v___y_1932_ = v_a_1332_;
v___y_1933_ = v_a_1333_;
v___y_1934_ = v_a_1334_;
goto v___jp_1930_;
}
else
{
lean_dec(v_val_1929_);
lean_del_object(v___x_1927_);
lean_dec(v_declName_1329_);
return v___x_1952_;
}
}
v___jp_1930_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v___x_1935_ = lean_array_get_size(v_val_1929_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_nat_dec_lt(v___x_1893_, v___x_1935_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1939_; 
lean_dec(v_val_1929_);
lean_dec(v_declName_1329_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1936_);
v___x_1939_ = v___x_1927_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1936_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
else
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_nat_dec_le(v___x_1935_, v___x_1935_);
if (v___x_1941_ == 0)
{
if (v___x_1937_ == 0)
{
lean_object* v___x_1943_; 
lean_dec(v_val_1929_);
lean_dec(v_declName_1329_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1936_);
v___x_1943_ = v___x_1927_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1936_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
else
{
size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
lean_del_object(v___x_1927_);
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = lean_usize_of_nat(v___x_1935_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1329_, v_val_1929_, v___x_1945_, v___x_1946_, v___x_1936_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v_val_1929_);
return v___x_1947_;
}
}
else
{
size_t v___x_1948_; size_t v___x_1949_; lean_object* v___x_1950_; 
lean_del_object(v___x_1927_);
v___x_1948_ = ((size_t)0ULL);
v___x_1949_ = lean_usize_of_nat(v___x_1935_);
v___x_1950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1329_, v_val_1929_, v___x_1948_, v___x_1949_, v___x_1936_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v_val_1929_);
return v___x_1950_;
}
}
}
}
else
{
lean_object* v___x_1953_; 
lean_del_object(v___x_1927_);
lean_dec(v_a_1925_);
lean_inc(v_mvarId_1330_);
v___x_1953_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1330_, v_hasTrace_1343_, v_hasTrace_1343_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref(v___x_1953_);
if (lean_obj_tag(v_a_1954_) == 1)
{
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1955_; lean_object* v___x_1956_; 
v_val_1955_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref(v_a_1954_);
v___x_1956_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1329_, v_val_1955_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1956_;
}
else
{
lean_object* v_val_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_val_1957_ = lean_ctor_get(v_a_1954_, 0);
lean_inc(v_val_1957_);
lean_dec_ref(v_a_1954_);
v___x_1958_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1959_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1958_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v___x_1959_);
v___x_1960_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1329_, v_val_1957_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1960_;
}
else
{
lean_dec(v_val_1957_);
lean_dec(v_declName_1329_);
return v___x_1959_;
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
lean_dec(v_a_1954_);
lean_dec(v_declName_1329_);
v___x_1961_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1962_, 0, v_mvarId_1330_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 7);
lean_ctor_set(v___x_1908_, 1, v___x_1962_);
lean_ctor_set(v___x_1908_, 0, v___x_1961_);
v___x_1964_ = v___x_1908_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1964_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1965_;
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1967_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1953_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1953_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
}
else
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1983_; 
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1976_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1978_ = v___x_1924_;
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1924_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1983_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1981_; 
if (v_isShared_1979_ == 0)
{
v___x_1981_ = v___x_1978_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_a_1976_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1984_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1916_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1916_);
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
default: 
{
lean_del_object(v___x_1908_);
lean_del_object(v___x_1904_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_mvarId_1992_; 
v_mvarId_1992_ = lean_ctor_get(v_fst_1906_, 0);
lean_inc(v_mvarId_1992_);
lean_dec_ref(v_fst_1906_);
v_mvarId_1330_ = v_mvarId_1992_;
goto _start;
}
else
{
lean_object* v_mvarId_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v_mvarId_1994_ = lean_ctor_get(v_fst_1906_, 0);
lean_inc(v_mvarId_1994_);
lean_dec_ref(v_fst_1906_);
v___x_1995_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1996_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1995_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_dec_ref(v___x_1996_);
v_mvarId_1330_ = v_mvarId_1994_;
goto _start;
}
else
{
lean_dec(v_mvarId_1994_);
lean_dec(v_declName_1329_);
return v___x_1996_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_2001_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1901_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1901_);
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
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_2009_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1898_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1898_);
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
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_2017_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1880_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1880_);
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
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_2025_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_1872_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_1872_);
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
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_2033_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1864_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1864_);
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
else
{
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
goto v___jp_1339_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2041_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2042_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_2041_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_dec_ref(v___x_2042_);
goto v___jp_1339_;
}
else
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_2043_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_1861_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_1861_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
goto v___jp_1336_;
}
else
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2052_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_2051_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_dec_ref(v___x_2052_);
goto v___jp_1336_;
}
else
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_2053_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_1858_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_1858_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
goto v___jp_1590_;
}
}
else
{
goto v___jp_1590_;
}
v___jp_1531_:
{
lean_object* v___x_1535_; double v___x_1536_; double v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1535_ = lean_io_get_num_heartbeats();
v___x_1536_ = lean_float_of_nat(v___y_1533_);
v___x_1537_ = lean_float_of_nat(v___x_1535_);
v___x_1538_ = lean_box_float(v___x_1536_);
v___x_1539_ = lean_box_float(v___x_1537_);
v___x_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1541_, 0, v_a_1534_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1527_, v_hasTrace_1343_, v___x_1528_, v_options_1342_, v___x_1530_, v___y_1532_, v___f_1526_, v___x_1541_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1542_;
}
v___jp_1543_:
{
lean_object* v___x_1547_; 
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1546_);
v___y_1532_ = v___y_1544_;
v___y_1533_ = v___y_1545_;
v_a_1534_ = v___x_1547_;
goto v___jp_1531_;
}
v___jp_1548_:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1551_);
v___y_1532_ = v___y_1549_;
v___y_1533_ = v___y_1550_;
v_a_1534_ = v___x_1552_;
goto v___jp_1531_;
}
v___jp_1553_:
{
if (lean_obj_tag(v___y_1556_) == 0)
{
lean_object* v_a_1557_; 
v_a_1557_ = lean_ctor_get(v___y_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___y_1556_);
v___y_1549_ = v___y_1554_;
v___y_1550_ = v___y_1555_;
v_a_1551_ = v_a_1557_;
goto v___jp_1548_;
}
else
{
lean_object* v_a_1558_; 
v_a_1558_ = lean_ctor_get(v___y_1556_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___y_1556_);
v___y_1544_ = v___y_1554_;
v___y_1545_ = v___y_1555_;
v_a_1546_ = v_a_1558_;
goto v___jp_1543_;
}
}
v___jp_1559_:
{
lean_object* v___x_1563_; double v___x_1564_; double v___x_1565_; double v___x_1566_; double v___x_1567_; double v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1563_ = lean_io_mono_nanos_now();
v___x_1564_ = lean_float_of_nat(v___y_1560_);
v___x_1565_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1566_ = lean_float_div(v___x_1564_, v___x_1565_);
v___x_1567_ = lean_float_of_nat(v___x_1563_);
v___x_1568_ = lean_float_div(v___x_1567_, v___x_1565_);
v___x_1569_ = lean_box_float(v___x_1566_);
v___x_1570_ = lean_box_float(v___x_1568_);
v___x_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_a_1562_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1527_, v_hasTrace_1343_, v___x_1528_, v_options_1342_, v___x_1530_, v___y_1561_, v___f_1526_, v___x_1572_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
return v___x_1573_;
}
v___jp_1574_:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_a_1577_);
v___y_1560_ = v___y_1575_;
v___y_1561_ = v___y_1576_;
v_a_1562_ = v___x_1578_;
goto v___jp_1559_;
}
v___jp_1579_:
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1583_, 0, v_a_1582_);
v___y_1560_ = v___y_1580_;
v___y_1561_ = v___y_1581_;
v_a_1562_ = v___x_1583_;
goto v___jp_1559_;
}
v___jp_1584_:
{
if (lean_obj_tag(v___y_1587_) == 0)
{
lean_object* v_a_1588_; 
v_a_1588_ = lean_ctor_get(v___y_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v___y_1587_);
v___y_1575_ = v___y_1585_;
v___y_1576_ = v___y_1586_;
v_a_1577_ = v_a_1588_;
goto v___jp_1574_;
}
else
{
lean_object* v_a_1589_; 
v_a_1589_ = lean_ctor_get(v___y_1587_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___y_1587_);
v___y_1580_ = v___y_1585_;
v___y_1581_ = v___y_1586_;
v_a_1582_ = v_a_1589_;
goto v___jp_1579_;
}
}
v___jp_1590_:
{
lean_object* v___x_1591_; 
v___x_1591_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1334_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1591_);
v___x_1593_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1594_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1342_, v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1330_);
v___x_1596_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; uint8_t v___x_1598_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1596_);
v___x_1598_ = lean_unbox(v_a_1597_);
lean_dec(v_a_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; 
lean_inc(v_mvarId_1330_);
v___x_1599_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; uint8_t v___x_1601_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v___x_1601_ = lean_unbox(v_a_1600_);
lean_dec(v_a_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_inc(v_mvarId_1330_);
v___x_1602_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_a_1603_; 
v_a_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1603_);
lean_dec_ref(v___x_1602_);
if (lean_obj_tag(v_a_1603_) == 1)
{
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1604_; lean_object* v___x_1605_; 
v_val_1604_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_val_1604_);
lean_dec_ref(v_a_1603_);
v___x_1605_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1604_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1605_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_val_1606_ = lean_ctor_get(v_a_1603_, 0);
lean_inc(v_val_1606_);
lean_dec_ref(v_a_1603_);
v___x_1607_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1608_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1607_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v___x_1609_; 
lean_dec_ref(v___x_1608_);
v___x_1609_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1606_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1609_;
goto v___jp_1584_;
}
else
{
lean_dec(v_val_1606_);
lean_dec(v_declName_1329_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1608_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v___x_1610_; 
lean_dec(v_a_1603_);
lean_inc(v_mvarId_1330_);
v___x_1610_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1610_);
if (lean_obj_tag(v_a_1611_) == 1)
{
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1612_; lean_object* v___x_1613_; 
v_val_1612_ = lean_ctor_get(v_a_1611_, 0);
lean_inc(v_val_1612_);
lean_dec_ref(v_a_1611_);
v___x_1613_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1612_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1613_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v_val_1614_ = lean_ctor_get(v_a_1611_, 0);
lean_inc(v_val_1614_);
lean_dec_ref(v_a_1611_);
v___x_1615_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1616_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1615_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v___x_1617_; 
lean_dec_ref(v___x_1616_);
v___x_1617_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1614_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1617_;
goto v___jp_1584_;
}
else
{
lean_dec(v_val_1614_);
lean_dec(v_declName_1329_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1616_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v___x_1618_; 
lean_dec(v_a_1611_);
lean_inc(v_mvarId_1330_);
v___x_1618_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1330_, v_hasTrace_1343_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
if (lean_obj_tag(v_a_1619_) == 1)
{
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1620_; lean_object* v___x_1621_; 
v_val_1620_ = lean_ctor_get(v_a_1619_, 0);
lean_inc(v_val_1620_);
lean_dec_ref(v_a_1619_);
v___x_1621_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1620_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1621_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v_val_1622_ = lean_ctor_get(v_a_1619_, 0);
lean_inc(v_val_1622_);
lean_dec_ref(v_a_1619_);
v___x_1623_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1624_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1623_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v___x_1625_; 
lean_dec_ref(v___x_1624_);
v___x_1625_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1622_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1625_;
goto v___jp_1584_;
}
else
{
lean_dec(v_val_1622_);
lean_dec(v_declName_1329_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1624_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec(v_a_1619_);
v___x_1626_ = lean_unsigned_to_nat(100000u);
v___x_1627_ = lean_unsigned_to_nat(2u);
v___x_1628_ = 0;
v___x_1629_ = lean_box(0);
v___x_1630_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1630_, 0, v___x_1626_);
lean_ctor_set(v___x_1630_, 1, v___x_1627_);
lean_ctor_set(v___x_1630_, 2, v___x_1629_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 1, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 2, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 3, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 4, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 5, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 6, v___x_1628_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 7, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 8, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 9, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 10, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 11, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 12, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 13, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 14, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 15, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 16, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 17, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 18, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 19, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 20, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 21, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 22, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 23, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 24, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 25, v_hasTrace_1343_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 26, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 27, v___x_1594_);
lean_ctor_set_uint8(v___x_1630_, sizeof(void*)*3 + 28, v___x_1594_);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1633_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1634_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1635_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*2, v_hasTrace_1343_);
v___x_1636_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1630_, v___x_1632_, v___x_1635_, v_a_1331_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1330_);
v___x_1639_ = l_Lean_Meta_simpTargetStar(v_mvarId_1330_, v_a_1637_, v___x_1632_, v___x_1629_, v___x_1638_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_fst_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1695_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
v_fst_1641_ = lean_ctor_get(v_a_1640_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_a_1640_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v_a_1640_, 1);
lean_dec(v_unused_1696_);
v___x_1643_ = v_a_1640_;
v_isShared_1644_ = v_isSharedCheck_1695_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_fst_1641_);
lean_dec(v_a_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1695_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
switch(lean_obj_tag(v_fst_1641_))
{
case 0:
{
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_box(0);
v___y_1575_ = v___x_1595_;
v___y_1576_ = v_a_1592_;
v_a_1577_ = v___x_1645_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1647_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1646_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1647_;
goto v___jp_1584_;
}
}
case 1:
{
lean_object* v___x_1648_; 
lean_inc(v_declName_1329_);
lean_inc(v_mvarId_1330_);
v___x_1648_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1330_, v_declName_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
if (lean_obj_tag(v_a_1649_) == 1)
{
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1650_; lean_object* v___x_1651_; 
v_val_1650_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_val_1650_);
lean_dec_ref(v_a_1649_);
v___x_1651_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1650_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1651_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v_val_1652_ = lean_ctor_get(v_a_1649_, 0);
lean_inc(v_val_1652_);
lean_dec_ref(v_a_1649_);
v___x_1653_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1654_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1653_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1654_) == 0)
{
lean_object* v___x_1655_; 
lean_dec_ref(v___x_1654_);
v___x_1655_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1652_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1655_;
goto v___jp_1584_;
}
else
{
lean_dec(v_val_1652_);
lean_dec(v_declName_1329_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1654_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v___x_1656_; 
lean_dec(v_a_1649_);
lean_inc(v_mvarId_1330_);
v___x_1656_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
if (lean_obj_tag(v_a_1657_) == 1)
{
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_val_1658_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_val_1658_);
lean_dec_ref(v_a_1657_);
v___x_1659_ = lean_box(0);
v___x_1660_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1658_, v___x_1631_, v_declName_1329_, v___x_1659_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_val_1658_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1660_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_val_1661_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_val_1661_);
lean_dec_ref(v_a_1657_);
v___x_1662_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1663_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1662_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v_a_1664_; lean_object* v___x_1665_; 
v_a_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_a_1664_);
lean_dec_ref(v___x_1663_);
v___x_1665_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1661_, v___x_1631_, v_declName_1329_, v_a_1664_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_val_1661_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1665_;
goto v___jp_1584_;
}
else
{
lean_dec(v_val_1661_);
lean_dec(v_declName_1329_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1663_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_a_1657_);
lean_inc(v_mvarId_1330_);
v___x_1666_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1330_, v_hasTrace_1343_, v_hasTrace_1343_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1685_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1669_ = v___x_1666_;
v_isShared_1670_ = v_isSharedCheck_1685_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1685_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
if (lean_obj_tag(v_a_1667_) == 1)
{
lean_del_object(v___x_1669_);
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1671_; lean_object* v___x_1672_; 
v_val_1671_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_val_1671_);
lean_dec_ref(v_a_1667_);
v___x_1672_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1329_, v_val_1671_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1672_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_val_1673_ = lean_ctor_get(v_a_1667_, 0);
lean_inc(v_val_1673_);
lean_dec_ref(v_a_1667_);
v___x_1674_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1675_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1674_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; 
lean_dec_ref(v___x_1675_);
v___x_1676_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1329_, v_val_1673_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1676_;
goto v___jp_1584_;
}
else
{
lean_dec(v_val_1673_);
lean_dec(v_declName_1329_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1675_;
goto v___jp_1584_;
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_dec(v_a_1667_);
lean_dec(v_declName_1329_);
v___x_1677_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1670_ == 0)
{
lean_ctor_set_tag(v___x_1669_, 1);
lean_ctor_set(v___x_1669_, 0, v_mvarId_1330_);
v___x_1679_ = v___x_1669_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_mvarId_1330_);
v___x_1679_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 7);
lean_ctor_set(v___x_1643_, 1, v___x_1679_);
lean_ctor_set(v___x_1643_, 0, v___x_1677_);
v___x_1681_ = v___x_1643_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1681_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1682_;
goto v___jp_1584_;
}
}
}
}
}
else
{
lean_object* v_a_1686_; 
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1686_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1666_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1686_;
goto v___jp_1579_;
}
}
}
else
{
lean_object* v_a_1687_; 
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1687_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1656_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1687_;
goto v___jp_1579_;
}
}
}
else
{
lean_object* v_a_1688_; 
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1688_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1648_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1688_;
goto v___jp_1579_;
}
}
default: 
{
lean_del_object(v___x_1643_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_mvarId_1689_; lean_object* v___x_1690_; 
v_mvarId_1689_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_mvarId_1689_);
lean_dec_ref(v_fst_1641_);
v___x_1690_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_mvarId_1689_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1690_;
goto v___jp_1584_;
}
else
{
lean_object* v_mvarId_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_mvarId_1691_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_mvarId_1691_);
lean_dec_ref(v_fst_1641_);
v___x_1692_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1693_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1692_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v___x_1694_; 
lean_dec_ref(v___x_1693_);
v___x_1694_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_mvarId_1691_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1694_;
goto v___jp_1584_;
}
else
{
lean_dec(v_mvarId_1691_);
lean_dec(v_declName_1329_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1693_;
goto v___jp_1584_;
}
}
}
}
}
}
else
{
lean_object* v_a_1697_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1697_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1639_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1697_;
goto v___jp_1579_;
}
}
else
{
lean_object* v_a_1698_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1698_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1636_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1698_;
goto v___jp_1579_;
}
}
}
else
{
lean_object* v_a_1699_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1699_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1699_);
lean_dec_ref(v___x_1618_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1699_;
goto v___jp_1579_;
}
}
}
else
{
lean_object* v_a_1700_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1700_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v___x_1610_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1700_;
goto v___jp_1579_;
}
}
}
else
{
lean_object* v_a_1701_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1701_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_a_1701_);
lean_dec_ref(v___x_1602_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1701_;
goto v___jp_1579_;
}
}
else
{
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_box(0);
v___x_1703_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1702_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1703_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1705_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1704_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1706_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1707_;
goto v___jp_1584_;
}
else
{
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1705_;
goto v___jp_1584_;
}
}
}
}
else
{
lean_object* v_a_1708_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1708_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___x_1599_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1708_;
goto v___jp_1579_;
}
}
else
{
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1709_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1710_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1712_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1711_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1712_);
v___x_1714_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1713_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1714_;
goto v___jp_1584_;
}
else
{
v___y_1585_ = v___x_1595_;
v___y_1586_ = v_a_1592_;
v___y_1587_ = v___x_1712_;
goto v___jp_1584_;
}
}
}
}
else
{
lean_object* v_a_1715_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1715_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1715_);
lean_dec_ref(v___x_1596_);
v___y_1580_ = v___x_1595_;
v___y_1581_ = v_a_1592_;
v_a_1582_ = v_a_1715_;
goto v___jp_1579_;
}
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1330_);
v___x_1717_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; uint8_t v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = lean_unbox(v_a_1718_);
lean_dec(v_a_1718_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; 
lean_inc(v_mvarId_1330_);
v___x_1720_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = lean_unbox(v_a_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_inc(v_mvarId_1330_);
v___x_1723_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1723_);
if (lean_obj_tag(v_a_1724_) == 1)
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1725_; lean_object* v___x_1726_; 
v_val_1725_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_val_1725_);
lean_dec_ref(v_a_1724_);
v___x_1726_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1725_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1726_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_val_1727_ = lean_ctor_get(v_a_1724_, 0);
lean_inc(v_val_1727_);
lean_dec_ref(v_a_1724_);
v___x_1728_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1729_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1728_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v___x_1729_);
v___x_1730_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1727_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1730_;
goto v___jp_1553_;
}
else
{
lean_dec(v_val_1727_);
lean_dec(v_declName_1329_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1729_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_a_1724_);
lean_inc(v_mvarId_1330_);
v___x_1731_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref(v___x_1731_);
if (lean_obj_tag(v_a_1732_) == 1)
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1733_; lean_object* v___x_1734_; 
v_val_1733_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_val_1733_);
lean_dec_ref(v_a_1732_);
v___x_1734_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1733_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1734_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_val_1735_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_val_1735_);
lean_dec_ref(v_a_1732_);
v___x_1736_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1737_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1736_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v___x_1738_; 
lean_dec_ref(v___x_1737_);
v___x_1738_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1735_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1738_;
goto v___jp_1553_;
}
else
{
lean_dec(v_val_1735_);
lean_dec(v_declName_1329_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1737_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_a_1732_);
lean_inc(v_mvarId_1330_);
v___x_1739_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1330_, v___x_1594_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v___x_1739_);
if (lean_obj_tag(v_a_1740_) == 1)
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1741_; lean_object* v___x_1742_; 
v_val_1741_ = lean_ctor_get(v_a_1740_, 0);
lean_inc(v_val_1741_);
lean_dec_ref(v_a_1740_);
v___x_1742_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1741_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1742_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v_val_1743_ = lean_ctor_get(v_a_1740_, 0);
lean_inc(v_val_1743_);
lean_dec_ref(v_a_1740_);
v___x_1744_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1745_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1744_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1746_; 
lean_dec_ref(v___x_1745_);
v___x_1746_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1743_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1746_;
goto v___jp_1553_;
}
else
{
lean_dec(v_val_1743_);
lean_dec(v_declName_1329_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1745_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; uint8_t v___x_1753_; uint8_t v___x_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; uint8_t v___x_1760_; uint8_t v___x_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
lean_dec(v_a_1740_);
v___x_1747_ = lean_unsigned_to_nat(100000u);
v___x_1748_ = lean_unsigned_to_nat(2u);
v___x_1749_ = 0;
v___x_1750_ = lean_box(0);
v___x_1751_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1751_, 0, v___x_1747_);
lean_ctor_set(v___x_1751_, 1, v___x_1748_);
lean_ctor_set(v___x_1751_, 2, v___x_1750_);
v___x_1752_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3, v___x_1752_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 1, v___x_1594_);
v___x_1753_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 2, v___x_1753_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 3, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 4, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 5, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 6, v___x_1749_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 7, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 8, v___x_1594_);
v___x_1754_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 9, v___x_1754_);
v___x_1755_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 10, v___x_1755_);
v___x_1756_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 11, v___x_1756_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 12, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 13, v___x_1594_);
v___x_1757_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 14, v___x_1757_);
v___x_1758_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 15, v___x_1758_);
v___x_1759_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 16, v___x_1759_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 17, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 18, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 19, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 20, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 21, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 22, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 23, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 24, v___x_1594_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 25, v___x_1594_);
v___x_1760_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 26, v___x_1760_);
v___x_1761_ = lean_unbox(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 27, v___x_1761_);
v___x_1762_ = lean_unbox(v_a_1721_);
lean_dec(v_a_1721_);
lean_ctor_set_uint8(v___x_1751_, sizeof(void*)*3 + 28, v___x_1762_);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1765_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1766_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1767_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2, v___x_1594_);
v___x_1768_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1751_, v___x_1764_, v___x_1767_, v_a_1331_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1330_);
v___x_1771_ = l_Lean_Meta_simpTargetStar(v_mvarId_1330_, v_a_1769_, v___x_1764_, v___x_1750_, v___x_1770_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v_fst_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1827_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1771_);
v_fst_1773_ = lean_ctor_get(v_a_1772_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_a_1772_, 1);
lean_dec(v_unused_1828_);
v___x_1775_ = v_a_1772_;
v_isShared_1776_ = v_isSharedCheck_1827_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_fst_1773_);
lean_dec(v_a_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1827_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
switch(lean_obj_tag(v_fst_1773_))
{
case 0:
{
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_box(0);
v___y_1549_ = v_a_1592_;
v___y_1550_ = v___x_1716_;
v_a_1551_ = v___x_1777_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1779_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1778_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1779_;
goto v___jp_1553_;
}
}
case 1:
{
lean_object* v___x_1780_; 
lean_inc(v_declName_1329_);
lean_inc(v_mvarId_1330_);
v___x_1780_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1330_, v_declName_1329_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1780_);
if (lean_obj_tag(v_a_1781_) == 1)
{
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1782_; lean_object* v___x_1783_; 
v_val_1782_ = lean_ctor_get(v_a_1781_, 0);
lean_inc(v_val_1782_);
lean_dec_ref(v_a_1781_);
v___x_1783_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1782_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1783_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_val_1784_ = lean_ctor_get(v_a_1781_, 0);
lean_inc(v_val_1784_);
lean_dec_ref(v_a_1781_);
v___x_1785_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1786_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1785_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v___x_1787_; 
lean_dec_ref(v___x_1786_);
v___x_1787_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_val_1784_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1787_;
goto v___jp_1553_;
}
else
{
lean_dec(v_val_1784_);
lean_dec(v_declName_1329_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1786_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1788_; 
lean_dec(v_a_1781_);
lean_inc(v_mvarId_1330_);
v___x_1788_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1788_);
if (lean_obj_tag(v_a_1789_) == 1)
{
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v_val_1790_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_val_1790_);
lean_dec_ref(v_a_1789_);
v___x_1791_ = lean_box(0);
v___x_1792_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1790_, v___x_1763_, v_declName_1329_, v___x_1791_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_val_1790_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1792_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_val_1793_ = lean_ctor_get(v_a_1789_, 0);
lean_inc(v_val_1793_);
lean_dec_ref(v_a_1789_);
v___x_1794_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1795_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1794_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; lean_object* v___x_1797_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1793_, v___x_1763_, v_declName_1329_, v_a_1796_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
lean_dec(v_val_1793_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1797_;
goto v___jp_1553_;
}
else
{
lean_dec(v_val_1793_);
lean_dec(v_declName_1329_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1795_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1798_; 
lean_dec(v_a_1789_);
lean_inc(v_mvarId_1330_);
v___x_1798_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1330_, v___x_1594_, v___x_1594_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1817_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1817_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1817_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
if (lean_obj_tag(v_a_1799_) == 1)
{
lean_del_object(v___x_1801_);
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_val_1803_; lean_object* v___x_1804_; 
v_val_1803_ = lean_ctor_get(v_a_1799_, 0);
lean_inc(v_val_1803_);
lean_dec_ref(v_a_1799_);
v___x_1804_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1329_, v_val_1803_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1804_;
goto v___jp_1553_;
}
else
{
lean_object* v_val_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_val_1805_ = lean_ctor_get(v_a_1799_, 0);
lean_inc(v_val_1805_);
lean_dec_ref(v_a_1799_);
v___x_1806_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1807_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1806_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v___x_1808_; 
lean_dec_ref(v___x_1807_);
v___x_1808_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1329_, v_val_1805_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1808_;
goto v___jp_1553_;
}
else
{
lean_dec(v_val_1805_);
lean_dec(v_declName_1329_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1807_;
goto v___jp_1553_;
}
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
lean_dec(v_a_1799_);
lean_dec(v_declName_1329_);
v___x_1809_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 1);
lean_ctor_set(v___x_1801_, 0, v_mvarId_1330_);
v___x_1811_ = v___x_1801_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_mvarId_1330_);
v___x_1811_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 7);
lean_ctor_set(v___x_1775_, 1, v___x_1811_);
lean_ctor_set(v___x_1775_, 0, v___x_1809_);
v___x_1813_ = v___x_1775_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1813_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1814_;
goto v___jp_1553_;
}
}
}
}
}
else
{
lean_object* v_a_1818_; 
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1818_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1798_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1818_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1819_; 
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1819_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1788_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1819_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1820_; 
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1820_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1780_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1820_;
goto v___jp_1543_;
}
}
default: 
{
lean_del_object(v___x_1775_);
lean_dec(v_mvarId_1330_);
if (v___x_1530_ == 0)
{
lean_object* v_mvarId_1821_; lean_object* v___x_1822_; 
v_mvarId_1821_ = lean_ctor_get(v_fst_1773_, 0);
lean_inc(v_mvarId_1821_);
lean_dec_ref(v_fst_1773_);
v___x_1822_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_mvarId_1821_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1822_;
goto v___jp_1553_;
}
else
{
lean_object* v_mvarId_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v_mvarId_1823_ = lean_ctor_get(v_fst_1773_, 0);
lean_inc(v_mvarId_1823_);
lean_dec_ref(v_fst_1773_);
v___x_1824_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1825_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1824_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref(v___x_1825_);
v___x_1826_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1329_, v_mvarId_1823_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1826_;
goto v___jp_1553_;
}
else
{
lean_dec(v_mvarId_1823_);
lean_dec(v_declName_1329_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1825_;
goto v___jp_1553_;
}
}
}
}
}
}
else
{
lean_object* v_a_1829_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1829_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1771_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1829_;
goto v___jp_1543_;
}
}
else
{
lean_object* v_a_1830_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1830_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1768_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1830_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1831_; 
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1831_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1739_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1831_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1832_; 
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1832_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1731_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1832_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1833_; 
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1833_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1833_);
lean_dec_ref(v___x_1723_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1833_;
goto v___jp_1543_;
}
}
else
{
lean_dec(v_a_1721_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1834_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1835_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1837_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1836_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___x_1839_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1838_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1839_;
goto v___jp_1553_;
}
else
{
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1837_;
goto v___jp_1553_;
}
}
}
}
else
{
lean_object* v_a_1840_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1840_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1720_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1840_;
goto v___jp_1543_;
}
}
else
{
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1841_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1842_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1844_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1527_, v___x_1843_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1845_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_);
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1846_;
goto v___jp_1553_;
}
else
{
v___y_1554_ = v_a_1592_;
v___y_1555_ = v___x_1716_;
v___y_1556_ = v___x_1844_;
goto v___jp_1553_;
}
}
}
}
else
{
lean_object* v_a_1847_; 
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1847_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1717_);
v___y_1544_ = v_a_1592_;
v___y_1545_ = v___x_1716_;
v_a_1546_ = v_a_1847_;
goto v___jp_1543_;
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec_ref(v___f_1526_);
lean_dec(v_mvarId_1330_);
lean_dec(v_declName_1329_);
v_a_1848_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1591_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1591_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
v___jp_1336_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_box(0);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
v___jp_1339_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_box(0);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2061_, lean_object* v_as_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
if (lean_obj_tag(v_as_2062_) == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_declName_2061_);
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
else
{
lean_object* v_head_2070_; lean_object* v_tail_2071_; lean_object* v___x_2072_; 
v_head_2070_ = lean_ctor_get(v_as_2062_, 0);
lean_inc(v_head_2070_);
v_tail_2071_ = lean_ctor_get(v_as_2062_, 1);
lean_inc(v_tail_2071_);
lean_dec_ref(v_as_2062_);
lean_inc(v_declName_2061_);
v___x_2072_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2061_, v_head_2070_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_dec_ref(v___x_2072_);
v_as_2062_ = v_tail_2071_;
goto _start;
}
else
{
lean_dec(v_tail_2071_);
lean_dec(v_declName_2061_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2074_, lean_object* v_as_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2074_, v_as_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2082_, lean_object* v_as_2083_, lean_object* v_i_2084_, lean_object* v_stop_2085_, lean_object* v_b_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
size_t v_i_boxed_2092_; size_t v_stop_boxed_2093_; lean_object* v_res_2094_; 
v_i_boxed_2092_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_stop_boxed_2093_ = lean_unbox_usize(v_stop_2085_);
lean_dec(v_stop_2085_);
v_res_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2082_, v_as_2083_, v_i_boxed_2092_, v_stop_boxed_2093_, v_b_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec_ref(v_as_2083_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2095_, lean_object* v___x_2096_, lean_object* v_declName_2097_, lean_object* v_____r_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2095_, v___x_2096_, v_declName_2097_, v_____r_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___x_2096_);
lean_dec_ref(v_val_2095_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2105_, lean_object* v_mvarId_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2105_, v_mvarId_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object* v_00_u03b1_2113_, lean_object* v_x_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_x_2114_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2121_, lean_object* v_x_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_00_u03b1_2121_, v_x_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2129_, uint8_t v_skipRealize_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v___x_2133_; lean_object* v_env_2134_; uint8_t v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2133_ = lean_st_ref_get(v___y_2131_);
v_env_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc_ref(v_env_2134_);
lean_dec(v___x_2133_);
v___x_2135_ = l_Lean_Environment_contains(v_env_2134_, v_constName_2129_, v_skipRealize_2130_);
v___x_2136_ = lean_box(v___x_2135_);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2138_, lean_object* v_skipRealize_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
uint8_t v_skipRealize_boxed_2142_; lean_object* v_res_2143_; 
v_skipRealize_boxed_2142_ = lean_unbox(v_skipRealize_2139_);
v_res_2143_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2138_, v_skipRealize_boxed_2142_, v___y_2140_);
lean_dec(v___y_2140_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2144_, uint8_t v_skipRealize_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2144_, v_skipRealize_2145_, v___y_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2152_, lean_object* v_skipRealize_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_skipRealize_boxed_2159_; lean_object* v_res_2160_; 
v_skipRealize_boxed_2159_ = lean_unbox(v_skipRealize_2153_);
v_res_2160_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2152_, v_skipRealize_boxed_2159_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2161_, lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v_snd_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___x_2170_; 
lean_inc_ref(v_snd_2161_);
v___x_2170_ = l_Lean_Meta_mkCongrArg(v_snd_2161_, v___x_2162_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
v___x_2172_ = l_Lean_Expr_app___override(v_snd_2161_, v___x_2163_);
v___x_2173_ = l_Lean_MVarId_replaceTargetEq(v_snd_2164_, v___x_2172_, v_a_2171_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2173_;
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_snd_2164_);
lean_dec_ref(v___x_2163_);
lean_dec_ref(v_snd_2161_);
v_a_2174_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2170_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2170_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2182_, lean_object* v___x_2183_, lean_object* v___x_2184_, lean_object* v_snd_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2182_, v___x_2183_, v___x_2184_, v_snd_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
return v_res_2191_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2204_ = l_Lean_stringToMessageData(v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2206_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2207_ = l_Lean_stringToMessageData(v___x_2206_);
return v___x_2207_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2209_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2210_ = l_Lean_stringToMessageData(v___x_2209_);
return v___x_2210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2213_ = l_Lean_stringToMessageData(v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2214_, lean_object* v___x_2215_, lean_object* v_cls_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v___x_2222_; 
lean_inc(v_mvarId_2214_);
v___x_2222_ = l_Lean_MVarId_getType(v_mvarId_2214_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2224_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2223_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v_fst_2226_; lean_object* v_snd_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2380_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
v_fst_2226_ = lean_ctor_get(v_a_2225_, 0);
v_snd_2227_ = lean_ctor_get(v_a_2225_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2229_ = v_a_2225_;
v_isShared_2230_ = v_isSharedCheck_2380_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_snd_2227_);
lean_inc(v_fst_2226_);
lean_dec(v_a_2225_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2380_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2379_; 
v___x_2231_ = l_Lean_Expr_getAppFn(v_fst_2226_);
v___x_2232_ = l_Lean_Expr_constName_x21(v___x_2231_);
v___x_2233_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2234_ = l_Lean_Name_str___override(v___x_2232_, v___x_2233_);
v___x_2235_ = 1;
lean_inc(v___x_2234_);
v___x_2236_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2234_, v___x_2235_, v___y_2220_);
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2239_ = v___x_2236_;
v_isShared_2240_ = v_isSharedCheck_2379_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2379_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v_nargs_2241_; lean_object* v___x_2242_; lean_object* v_dummy_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; uint8_t v___x_2362_; 
v_nargs_2241_ = l_Lean_Expr_getAppNumArgs(v_fst_2226_);
v___x_2242_ = l_Lean_Expr_constLevels_x21(v___x_2231_);
lean_dec_ref(v___x_2231_);
v_dummy_2243_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
lean_inc(v_nargs_2241_);
v___x_2244_ = lean_mk_array(v_nargs_2241_, v_dummy_2243_);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_sub(v_nargs_2241_, v___x_2245_);
lean_dec(v_nargs_2241_);
v___x_2247_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2226_, v___x_2244_, v___x_2246_);
v___x_2362_ = lean_unbox(v_a_2237_);
lean_dec(v_a_2237_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v___x_2247_);
lean_dec(v___x_2242_);
lean_del_object(v___x_2239_);
lean_del_object(v___x_2229_);
lean_dec(v_snd_2227_);
lean_dec(v_cls_2216_);
v___x_2363_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2364_ = l_Lean_MessageData_ofName(v___x_2234_);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v_mvarId_2214_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2369_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
v_a_2371_ = lean_ctor_get(v___x_2370_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___x_2370_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___x_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
v___y_2289_ = v___y_2217_;
v___y_2290_ = v___y_2218_;
v___y_2291_ = v___y_2219_;
v___y_2292_ = v___y_2220_;
goto v___jp_2288_;
}
v___jp_2248_:
{
lean_object* v___x_2257_; 
lean_inc(v___y_2256_);
lean_inc_ref(v___y_2255_);
lean_inc(v___y_2254_);
lean_inc_ref(v___y_2253_);
lean_inc_ref(v___y_2252_);
v___x_2257_ = lean_infer_type(v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v_a_2258_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2260_ = l_Lean_MVarId_define(v_mvarId_2214_, v___x_2259_, v_a_2258_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___x_2262_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
v___x_2262_ = l_Lean_Meta_intro1Core(v_a_2261_, v___y_2249_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v_fst_2264_; lean_object* v_snd_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
v_fst_2264_ = lean_ctor_get(v_a_2263_, 0);
lean_inc(v_fst_2264_);
v_snd_2265_ = lean_ctor_get(v_a_2263_, 1);
lean_inc_n(v_snd_2265_, 2);
lean_dec(v_a_2263_);
v___x_2266_ = l_Lean_Expr_appFn_x21(v___y_2250_);
lean_dec_ref(v___y_2250_);
v___x_2267_ = l_Lean_mkFVar(v_fst_2264_);
v___x_2268_ = l_Lean_Expr_app___override(v___x_2266_, v___x_2267_);
v___x_2269_ = l_Lean_mkAppN(v___y_2251_, v___x_2247_);
lean_dec_ref(v___x_2247_);
v___f_2270_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2270_, 0, v_snd_2227_);
lean_closure_set(v___f_2270_, 1, v___x_2269_);
lean_closure_set(v___f_2270_, 2, v___x_2268_);
lean_closure_set(v___f_2270_, 3, v_snd_2265_);
v___x_2271_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2265_, v___f_2270_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v___x_2271_;
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v___x_2247_);
lean_dec(v_snd_2227_);
v_a_2272_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2262_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2262_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v___x_2247_);
lean_dec(v_snd_2227_);
return v___x_2260_;
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec_ref(v___x_2247_);
lean_dec(v_snd_2227_);
lean_dec(v_mvarId_2214_);
v_a_2280_ = lean_ctor_get(v___x_2257_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2257_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2257_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2257_);
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
v___jp_2288_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_inc(v___x_2234_);
v___x_2293_ = l_Lean_mkConst(v___x_2234_, v___x_2242_);
lean_inc(v___y_2292_);
lean_inc_ref(v___y_2291_);
lean_inc(v___y_2290_);
lean_inc_ref(v___y_2289_);
lean_inc_ref(v___x_2293_);
v___x_2294_ = lean_infer_type(v___x_2293_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2294_);
v___x_2296_ = l_Lean_Meta_instantiateForall(v_a_2295_, v___x_2247_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2296_);
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2299_ = lean_unsigned_to_nat(3u);
v___x_2300_ = l_Lean_Expr_isAppOfArity(v_a_2297_, v___x_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_dec(v_a_2297_);
lean_dec_ref(v___x_2293_);
lean_dec_ref(v___x_2247_);
lean_dec(v_snd_2227_);
lean_dec(v_cls_2216_);
v___x_2301_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2302_ = l_Lean_MessageData_ofName(v___x_2234_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 7);
lean_ctor_set(v___x_2229_, 1, v___x_2302_);
lean_ctor_set(v___x_2229_, 0, v___x_2301_);
v___x_2304_ = v___x_2229_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v___x_2305_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set_tag(v___x_2239_, 1);
lean_ctor_set(v___x_2239_, 0, v_mvarId_2214_);
v___x_2308_ = v___x_2239_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_mvarId_2214_);
v___x_2308_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2306_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2309_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
return v___x_2310_;
}
}
}
else
{
lean_object* v_options_2313_; lean_object* v_inheritedTraceOptions_2314_; uint8_t v_hasTrace_2315_; lean_object* v___x_2316_; lean_object* v_nargs_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_del_object(v___x_2239_);
lean_dec(v___x_2234_);
v_options_2313_ = lean_ctor_get(v___y_2291_, 2);
v_inheritedTraceOptions_2314_ = lean_ctor_get(v___y_2291_, 13);
v_hasTrace_2315_ = lean_ctor_get_uint8(v_options_2313_, sizeof(void*)*1);
v___x_2316_ = l_Lean_Expr_appArg_x21(v_a_2297_);
lean_dec(v_a_2297_);
v_nargs_2317_ = l_Lean_Expr_getAppNumArgs(v___x_2316_);
lean_inc(v_nargs_2317_);
v___x_2318_ = lean_mk_array(v_nargs_2317_, v_dummy_2243_);
v___x_2319_ = lean_nat_sub(v_nargs_2317_, v___x_2245_);
lean_dec(v_nargs_2317_);
lean_inc_ref(v___x_2316_);
v___x_2320_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2316_, v___x_2318_, v___x_2319_);
v___x_2321_ = lean_array_get_size(v___x_2320_);
v___x_2322_ = lean_nat_sub(v___x_2321_, v___x_2245_);
v___x_2323_ = lean_array_get(v___x_2215_, v___x_2320_, v___x_2322_);
lean_dec(v___x_2322_);
lean_dec_ref(v___x_2320_);
if (v_hasTrace_2315_ == 0)
{
lean_del_object(v___x_2229_);
lean_dec(v_cls_2216_);
v___y_2249_ = v___x_2300_;
v___y_2250_ = v___x_2316_;
v___y_2251_ = v___x_2293_;
v___y_2252_ = v___x_2323_;
v___y_2253_ = v___y_2289_;
v___y_2254_ = v___y_2290_;
v___y_2255_ = v___y_2291_;
v___y_2256_ = v___y_2292_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2324_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2216_);
v___x_2325_ = l_Lean_Name_append(v___x_2324_, v_cls_2216_);
v___x_2326_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2314_, v_options_2313_, v___x_2325_);
lean_dec(v___x_2325_);
if (v___x_2326_ == 0)
{
lean_del_object(v___x_2229_);
lean_dec(v_cls_2216_);
v___y_2249_ = v___x_2300_;
v___y_2250_ = v___x_2316_;
v___y_2251_ = v___x_2293_;
v___y_2252_ = v___x_2323_;
v___y_2253_ = v___y_2289_;
v___y_2254_ = v___y_2290_;
v___y_2255_ = v___y_2291_;
v___y_2256_ = v___y_2292_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2327_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2328_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2323_);
v___x_2329_ = l_Lean_inlineExpr(v___x_2323_, v___x_2328_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set_tag(v___x_2229_, 7);
lean_ctor_set(v___x_2229_, 1, v___x_2329_);
lean_ctor_set(v___x_2229_, 0, v___x_2327_);
v___x_2331_ = v___x_2229_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2332_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2331_);
lean_ctor_set(v___x_2333_, 1, v___x_2332_);
lean_inc_ref(v___x_2316_);
v___x_2334_ = l_Lean_indentExpr(v___x_2316_);
v___x_2335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2216_, v___x_2335_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_dec_ref(v___x_2336_);
v___y_2249_ = v___x_2300_;
v___y_2250_ = v___x_2316_;
v___y_2251_ = v___x_2293_;
v___y_2252_ = v___x_2323_;
v___y_2253_ = v___y_2289_;
v___y_2254_ = v___y_2290_;
v___y_2255_ = v___y_2291_;
v___y_2256_ = v___y_2292_;
goto v___jp_2248_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v___x_2323_);
lean_dec_ref(v___x_2316_);
lean_dec_ref(v___x_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v___x_2247_);
lean_dec(v_snd_2227_);
lean_dec(v_mvarId_2214_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
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
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v___x_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v___x_2247_);
lean_del_object(v___x_2239_);
lean_dec(v___x_2234_);
lean_del_object(v___x_2229_);
lean_dec(v_snd_2227_);
lean_dec(v_cls_2216_);
lean_dec(v_mvarId_2214_);
v_a_2346_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2296_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2296_);
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
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v___x_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v___x_2247_);
lean_del_object(v___x_2239_);
lean_dec(v___x_2234_);
lean_del_object(v___x_2229_);
lean_dec(v_snd_2227_);
lean_dec(v_cls_2216_);
lean_dec(v_mvarId_2214_);
v_a_2354_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2294_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2294_);
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
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v_cls_2216_);
lean_dec(v_mvarId_2214_);
v_a_2381_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2224_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2224_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v_cls_2216_);
lean_dec(v_mvarId_2214_);
v_a_2389_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2222_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2222_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2397_, lean_object* v___x_2398_, lean_object* v_cls_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2397_, v___x_2398_, v_cls_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec_ref(v___x_2398_);
return v_res_2405_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2408_ = l_Lean_stringToMessageData(v___x_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2409_, lean_object* v_x_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_mvarId_2409_);
v___x_2418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2416_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2420_, lean_object* v_x_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2420_, v_x_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec_ref(v_x_2421_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2428_, lean_object* v_mvarId_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_options_2435_; lean_object* v_inheritedTraceOptions_2436_; uint8_t v_hasTrace_2437_; lean_object* v___x_2438_; lean_object* v_cls_2439_; lean_object* v___f_2440_; 
v_options_2435_ = lean_ctor_get(v_a_2432_, 2);
v_inheritedTraceOptions_2436_ = lean_ctor_get(v_a_2432_, 13);
v_hasTrace_2437_ = lean_ctor_get_uint8(v_options_2435_, sizeof(void*)*1);
v___x_2438_ = l_Lean_instInhabitedExpr;
v_cls_2439_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2429_);
v___f_2440_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2440_, 0, v_mvarId_2429_);
lean_closure_set(v___f_2440_, 1, v___x_2438_);
lean_closure_set(v___f_2440_, 2, v_cls_2439_);
if (v_hasTrace_2437_ == 0)
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2429_, v___f_2440_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
v___x_2443_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2428_, v_a_2442_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
return v___x_2443_;
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_declName_2428_);
v_a_2444_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2441_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2441_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
else
{
lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; uint8_t v___x_2455_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v_a_2459_; lean_object* v___y_2472_; lean_object* v___y_2473_; lean_object* v_a_2474_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v_a_2479_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v_a_2491_; 
lean_inc(v_mvarId_2429_);
v___f_2452_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2452_, 0, v_mvarId_2429_);
v___x_2453_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2454_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2436_, v_options_2435_, v___x_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = l_Lean_trace_profiler;
v___x_2527_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2435_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; 
lean_dec_ref(v___f_2452_);
v___x_2528_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2429_, v___f_2440_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v___x_2528_);
v___x_2530_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2428_, v_a_2529_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
return v___x_2530_;
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_declName_2428_);
v_a_2531_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2528_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2528_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
goto v___jp_2493_;
}
}
else
{
goto v___jp_2493_;
}
v___jp_2456_:
{
lean_object* v___x_2460_; double v___x_2461_; double v___x_2462_; double v___x_2463_; double v___x_2464_; double v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2460_ = lean_io_mono_nanos_now();
v___x_2461_ = lean_float_of_nat(v___y_2458_);
v___x_2462_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2463_ = lean_float_div(v___x_2461_, v___x_2462_);
v___x_2464_ = lean_float_of_nat(v___x_2460_);
v___x_2465_ = lean_float_div(v___x_2464_, v___x_2462_);
v___x_2466_ = lean_box_float(v___x_2463_);
v___x_2467_ = lean_box_float(v___x_2465_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2466_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v_a_2459_);
lean_ctor_set(v___x_2469_, 1, v___x_2468_);
v___x_2470_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2439_, v_hasTrace_2437_, v___x_2453_, v_options_2435_, v___x_2455_, v___y_2457_, v___f_2452_, v___x_2469_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
return v___x_2470_;
}
v___jp_2471_:
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v_a_2474_);
v___y_2457_ = v___y_2472_;
v___y_2458_ = v___y_2473_;
v_a_2459_ = v___x_2475_;
goto v___jp_2456_;
}
v___jp_2476_:
{
lean_object* v___x_2480_; double v___x_2481_; double v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2480_ = lean_io_get_num_heartbeats();
v___x_2481_ = lean_float_of_nat(v___y_2477_);
v___x_2482_ = lean_float_of_nat(v___x_2480_);
v___x_2483_ = lean_box_float(v___x_2481_);
v___x_2484_ = lean_box_float(v___x_2482_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2483_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2486_, 0, v_a_2479_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2439_, v_hasTrace_2437_, v___x_2453_, v_options_2435_, v___x_2455_, v___y_2478_, v___f_2452_, v___x_2486_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
return v___x_2487_;
}
v___jp_2488_:
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v_a_2491_);
v___y_2477_ = v___y_2489_;
v___y_2478_ = v___y_2490_;
v_a_2479_ = v___x_2492_;
goto v___jp_2476_;
}
v___jp_2493_:
{
lean_object* v___x_2494_; lean_object* v_a_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2494_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2433_);
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2497_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2435_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_io_mono_nanos_now();
v___x_2499_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2429_, v___f_2440_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; lean_object* v___x_2501_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref(v___x_2499_);
v___x_2501_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2428_, v_a_2500_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 1);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
v___y_2457_ = v_a_2495_;
v___y_2458_ = v___x_2498_;
v_a_2459_ = v___x_2507_;
goto v___jp_2456_;
}
}
}
else
{
lean_object* v_a_2510_; 
v_a_2510_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2510_);
lean_dec_ref(v___x_2501_);
v___y_2472_ = v_a_2495_;
v___y_2473_ = v___x_2498_;
v_a_2474_ = v_a_2510_;
goto v___jp_2471_;
}
}
else
{
lean_object* v_a_2511_; 
lean_dec(v_declName_2428_);
v_a_2511_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2511_);
lean_dec_ref(v___x_2499_);
v___y_2472_ = v_a_2495_;
v___y_2473_ = v___x_2498_;
v_a_2474_ = v_a_2511_;
goto v___jp_2471_;
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_io_get_num_heartbeats();
v___x_2513_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2429_, v___f_2440_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2513_);
v___x_2515_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2428_, v_a_2514_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
v___y_2477_ = v___x_2512_;
v___y_2478_ = v_a_2495_;
v_a_2479_ = v___x_2521_;
goto v___jp_2476_;
}
}
}
else
{
lean_object* v_a_2524_; 
v_a_2524_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2524_);
lean_dec_ref(v___x_2515_);
v___y_2489_ = v___x_2512_;
v___y_2490_ = v_a_2495_;
v_a_2491_ = v_a_2524_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2525_; 
lean_dec(v_declName_2428_);
v_a_2525_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2525_);
lean_dec_ref(v___x_2513_);
v___y_2489_ = v___x_2512_;
v___y_2490_ = v_a_2495_;
v_a_2491_ = v_a_2525_;
goto v___jp_2488_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2539_, lean_object* v_mvarId_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2539_, v_mvarId_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2547_, lean_object* v___y_2548_){
_start:
{
uint8_t v___x_2550_; 
v___x_2550_ = l_Lean_Expr_hasMVar(v_e_2547_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2551_, 0, v_e_2547_);
return v___x_2551_;
}
else
{
lean_object* v___x_2552_; lean_object* v_mctx_2553_; lean_object* v___x_2554_; lean_object* v_fst_2555_; lean_object* v_snd_2556_; lean_object* v___x_2557_; lean_object* v_cache_2558_; lean_object* v_zetaDeltaFVarIds_2559_; lean_object* v_postponed_2560_; lean_object* v_diag_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2570_; 
v___x_2552_ = lean_st_ref_get(v___y_2548_);
v_mctx_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_ref(v_mctx_2553_);
lean_dec(v___x_2552_);
v___x_2554_ = l_Lean_instantiateMVarsCore(v_mctx_2553_, v_e_2547_);
v_fst_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_fst_2555_);
v_snd_2556_ = lean_ctor_get(v___x_2554_, 1);
lean_inc(v_snd_2556_);
lean_dec_ref(v___x_2554_);
v___x_2557_ = lean_st_ref_take(v___y_2548_);
v_cache_2558_ = lean_ctor_get(v___x_2557_, 1);
v_zetaDeltaFVarIds_2559_ = lean_ctor_get(v___x_2557_, 2);
v_postponed_2560_ = lean_ctor_get(v___x_2557_, 3);
v_diag_2561_ = lean_ctor_get(v___x_2557_, 4);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2570_ == 0)
{
lean_object* v_unused_2571_; 
v_unused_2571_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2571_);
v___x_2563_ = v___x_2557_;
v_isShared_2564_ = v_isSharedCheck_2570_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_diag_2561_);
lean_inc(v_postponed_2560_);
lean_inc(v_zetaDeltaFVarIds_2559_);
lean_inc(v_cache_2558_);
lean_dec(v___x_2557_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2570_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v_snd_2556_);
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_snd_2556_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_cache_2558_);
lean_ctor_set(v_reuseFailAlloc_2569_, 2, v_zetaDeltaFVarIds_2559_);
lean_ctor_set(v_reuseFailAlloc_2569_, 3, v_postponed_2560_);
lean_ctor_set(v_reuseFailAlloc_2569_, 4, v_diag_2561_);
v___x_2566_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_st_ref_set(v___y_2548_, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_fst_2555_);
return v___x_2568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2572_, v___y_2573_);
lean_dec(v___y_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2576_, v___y_2578_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v___y_2584_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2590_, uint8_t v_allowLevelAssignments_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2591_, v_k_2590_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2597_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
v_a_2606_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2597_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2597_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2614_, lean_object* v_allowLevelAssignments_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2621_; lean_object* v_res_2622_; 
v_allowLevelAssignments_boxed_2621_ = lean_unbox(v_allowLevelAssignments_2615_);
v_res_2622_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2614_, v_allowLevelAssignments_boxed_2621_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2623_, lean_object* v_k_2624_, uint8_t v_allowLevelAssignments_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2624_, v_allowLevelAssignments_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_k_2633_, lean_object* v_allowLevelAssignments_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2640_; lean_object* v_res_2641_; 
v_allowLevelAssignments_boxed_2640_ = lean_unbox(v_allowLevelAssignments_2634_);
v_res_2641_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2632_, v_k_2633_, v_allowLevelAssignments_boxed_2640_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2642_, lean_object* v_e_2643_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = l_Lean_indentD(v_e_2643_);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2642_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2646_, lean_object* v___x_2647_, lean_object* v_declName_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2646_, v___x_2647_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = l_Lean_Expr_mvarId_x21(v_a_2655_);
v___x_2657_ = l_Lean_MVarId_intros(v___x_2656_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v_snd_2659_; lean_object* v___x_2660_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2657_);
v_snd_2659_ = lean_ctor_get(v_a_2658_, 1);
lean_inc_n(v_snd_2659_, 2);
lean_dec(v_a_2658_);
v___x_2660_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2659_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; uint8_t v___x_2662_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2660_);
v___x_2662_ = lean_unbox(v_a_2661_);
lean_dec(v_a_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2659_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2665_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
v___x_2665_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2648_, v_a_2664_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2666_; 
lean_dec_ref(v___x_2665_);
v___x_2666_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2655_, v___y_2650_);
return v___x_2666_;
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_a_2655_);
v_a_2667_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2665_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2665_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2655_);
lean_dec(v_declName_2648_);
v_a_2675_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2663_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2663_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v___x_2683_; 
lean_dec(v_snd_2659_);
lean_dec(v_declName_2648_);
v___x_2683_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2655_, v___y_2650_);
return v___x_2683_;
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_dec(v_snd_2659_);
lean_dec(v_a_2655_);
lean_dec(v_declName_2648_);
v_a_2684_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2660_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2660_);
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
lean_dec(v_a_2655_);
lean_dec(v_declName_2648_);
v_a_2692_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2657_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2657_);
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
lean_dec(v_declName_2648_);
return v___x_2654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2700_, lean_object* v___x_2701_, lean_object* v_declName_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2700_, v___x_2701_, v_declName_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2708_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2710_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2711_ = l_Lean_stringToMessageData(v___x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2719_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2720_ = l_Lean_indentExpr(v_type_2712_);
v___x_2721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2723_, lean_object* v_x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2723_, v_x_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec_ref(v_x_2724_);
return v_res_2730_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2731_){
_start:
{
if (lean_obj_tag(v_e_2731_) == 0)
{
uint8_t v___x_2732_; 
v___x_2732_ = 2;
return v___x_2732_;
}
else
{
uint8_t v___x_2733_; 
v___x_2733_ = 0;
return v___x_2733_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2734_){
_start:
{
uint8_t v_res_2735_; lean_object* v_r_2736_; 
v_res_2735_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2734_);
lean_dec_ref(v_e_2734_);
v_r_2736_ = lean_box(v_res_2735_);
return v_r_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2737_, uint8_t v_collapsed_2738_, lean_object* v_tag_2739_, lean_object* v_opts_2740_, uint8_t v_clsEnabled_2741_, lean_object* v_oldTraces_2742_, lean_object* v_msg_2743_, lean_object* v_resStartStop_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_fst_2750_; lean_object* v_snd_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2849_; 
v_fst_2750_ = lean_ctor_get(v_resStartStop_2744_, 0);
v_snd_2751_ = lean_ctor_get(v_resStartStop_2744_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_resStartStop_2744_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2753_ = v_resStartStop_2744_;
v_isShared_2754_ = v_isSharedCheck_2849_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snd_2751_);
lean_inc(v_fst_2750_);
lean_dec(v_resStartStop_2744_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2849_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v_data_2758_; lean_object* v_fst_2769_; lean_object* v_snd_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2848_; 
v_fst_2769_ = lean_ctor_get(v_snd_2751_, 0);
v_snd_2770_ = lean_ctor_get(v_snd_2751_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_snd_2751_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2772_ = v_snd_2751_;
v_isShared_2773_ = v_isSharedCheck_2848_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_snd_2770_);
lean_inc(v_fst_2769_);
lean_dec(v_snd_2751_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2848_;
goto v_resetjp_2771_;
}
v___jp_2755_:
{
lean_object* v___x_2759_; 
lean_inc(v___y_2756_);
v___x_2759_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_oldTraces_2742_, v_data_2758_, v___y_2756_, v___y_2757_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v___x_2759_);
v___x_2760_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_2750_);
return v___x_2760_;
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
lean_dec(v_fst_2750_);
v_a_2761_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2759_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2759_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___y_2777_; lean_object* v_a_2778_; uint8_t v___y_2802_; double v___y_2833_; 
v___x_2774_ = l_Lean_trace_profiler;
v___x_2775_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2740_, v___x_2774_);
if (v___x_2775_ == 0)
{
v___y_2802_ = v___x_2775_;
goto v___jp_2801_;
}
else
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2839_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2740_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; double v___x_2842_; double v___x_2843_; double v___x_2844_; 
v___x_2840_ = l_Lean_trace_profiler_threshold;
v___x_2841_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2740_, v___x_2840_);
v___x_2842_ = lean_float_of_nat(v___x_2841_);
v___x_2843_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4);
v___x_2844_ = lean_float_div(v___x_2842_, v___x_2843_);
v___y_2833_ = v___x_2844_;
goto v___jp_2832_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; double v___x_2847_; 
v___x_2845_ = l_Lean_trace_profiler_threshold;
v___x_2846_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2740_, v___x_2845_);
v___x_2847_ = lean_float_of_nat(v___x_2846_);
v___y_2833_ = v___x_2847_;
goto v___jp_2832_;
}
}
v___jp_2776_:
{
uint8_t v_result_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; 
v_result_2779_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2750_);
v___x_2780_ = l_Lean_TraceResult_toEmoji(v_result_2779_);
v___x_2781_ = l_Lean_stringToMessageData(v___x_2780_);
v___x_2782_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
if (v_isShared_2773_ == 0)
{
lean_ctor_set_tag(v___x_2772_, 7);
lean_ctor_set(v___x_2772_, 1, v___x_2782_);
lean_ctor_set(v___x_2772_, 0, v___x_2781_);
v___x_2784_ = v___x_2772_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2781_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v_m_2786_; 
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 7);
lean_ctor_set(v___x_2753_, 1, v_a_2778_);
lean_ctor_set(v___x_2753_, 0, v___x_2784_);
v_m_2786_ = v___x_2753_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2794_, 1, v_a_2778_);
v_m_2786_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; double v___x_2789_; lean_object* v_data_2790_; 
v___x_2787_ = lean_box(v_result_2779_);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
v___x_2789_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2739_);
lean_inc_ref(v___x_2788_);
lean_inc(v_cls_2737_);
v_data_2790_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2790_, 0, v_cls_2737_);
lean_ctor_set(v_data_2790_, 1, v___x_2788_);
lean_ctor_set(v_data_2790_, 2, v_tag_2739_);
lean_ctor_set_float(v_data_2790_, sizeof(void*)*3, v___x_2789_);
lean_ctor_set_float(v_data_2790_, sizeof(void*)*3 + 8, v___x_2789_);
lean_ctor_set_uint8(v_data_2790_, sizeof(void*)*3 + 16, v_collapsed_2738_);
if (v___x_2775_ == 0)
{
lean_dec_ref(v___x_2788_);
lean_dec(v_snd_2770_);
lean_dec(v_fst_2769_);
lean_dec_ref(v_tag_2739_);
lean_dec(v_cls_2737_);
v___y_2756_ = v___y_2777_;
v___y_2757_ = v_m_2786_;
v_data_2758_ = v_data_2790_;
goto v___jp_2755_;
}
else
{
lean_object* v_data_2791_; double v___x_2792_; double v___x_2793_; 
lean_dec_ref(v_data_2790_);
v_data_2791_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2791_, 0, v_cls_2737_);
lean_ctor_set(v_data_2791_, 1, v___x_2788_);
lean_ctor_set(v_data_2791_, 2, v_tag_2739_);
v___x_2792_ = lean_unbox_float(v_fst_2769_);
lean_dec(v_fst_2769_);
lean_ctor_set_float(v_data_2791_, sizeof(void*)*3, v___x_2792_);
v___x_2793_ = lean_unbox_float(v_snd_2770_);
lean_dec(v_snd_2770_);
lean_ctor_set_float(v_data_2791_, sizeof(void*)*3 + 8, v___x_2793_);
lean_ctor_set_uint8(v_data_2791_, sizeof(void*)*3 + 16, v_collapsed_2738_);
v___y_2756_ = v___y_2777_;
v___y_2757_ = v_m_2786_;
v_data_2758_ = v_data_2791_;
goto v___jp_2755_;
}
}
}
}
v___jp_2796_:
{
lean_object* v_ref_2797_; lean_object* v___x_2798_; 
v_ref_2797_ = lean_ctor_get(v___y_2747_, 5);
lean_inc(v___y_2748_);
lean_inc_ref(v___y_2747_);
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2745_);
lean_inc(v_fst_2750_);
v___x_2798_ = lean_apply_6(v_msg_2743_, v_fst_2750_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, lean_box(0));
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref(v___x_2798_);
v___y_2777_ = v_ref_2797_;
v_a_2778_ = v_a_2799_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_2800_; 
lean_dec_ref(v___x_2798_);
v___x_2800_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3);
v___y_2777_ = v_ref_2797_;
v_a_2778_ = v___x_2800_;
goto v___jp_2776_;
}
}
v___jp_2801_:
{
if (v_clsEnabled_2741_ == 0)
{
if (v___y_2802_ == 0)
{
lean_object* v___x_2803_; lean_object* v_traceState_2804_; lean_object* v_env_2805_; lean_object* v_nextMacroScope_2806_; lean_object* v_ngen_2807_; lean_object* v_auxDeclNGen_2808_; lean_object* v_cache_2809_; lean_object* v_messages_2810_; lean_object* v_infoState_2811_; lean_object* v_snapshotTasks_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2831_; 
lean_del_object(v___x_2772_);
lean_dec(v_snd_2770_);
lean_dec(v_fst_2769_);
lean_del_object(v___x_2753_);
lean_dec_ref(v_msg_2743_);
lean_dec_ref(v_tag_2739_);
lean_dec(v_cls_2737_);
v___x_2803_ = lean_st_ref_take(v___y_2748_);
v_traceState_2804_ = lean_ctor_get(v___x_2803_, 4);
v_env_2805_ = lean_ctor_get(v___x_2803_, 0);
v_nextMacroScope_2806_ = lean_ctor_get(v___x_2803_, 1);
v_ngen_2807_ = lean_ctor_get(v___x_2803_, 2);
v_auxDeclNGen_2808_ = lean_ctor_get(v___x_2803_, 3);
v_cache_2809_ = lean_ctor_get(v___x_2803_, 5);
v_messages_2810_ = lean_ctor_get(v___x_2803_, 6);
v_infoState_2811_ = lean_ctor_get(v___x_2803_, 7);
v_snapshotTasks_2812_ = lean_ctor_get(v___x_2803_, 8);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2814_ = v___x_2803_;
v_isShared_2815_ = v_isSharedCheck_2831_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_snapshotTasks_2812_);
lean_inc(v_infoState_2811_);
lean_inc(v_messages_2810_);
lean_inc(v_cache_2809_);
lean_inc(v_traceState_2804_);
lean_inc(v_auxDeclNGen_2808_);
lean_inc(v_ngen_2807_);
lean_inc(v_nextMacroScope_2806_);
lean_inc(v_env_2805_);
lean_dec(v___x_2803_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2831_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
uint64_t v_tid_2816_; lean_object* v_traces_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2830_; 
v_tid_2816_ = lean_ctor_get_uint64(v_traceState_2804_, sizeof(void*)*1);
v_traces_2817_ = lean_ctor_get(v_traceState_2804_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v_traceState_2804_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2819_ = v_traceState_2804_;
v_isShared_2820_ = v_isSharedCheck_2830_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_traces_2817_);
lean_dec(v_traceState_2804_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2830_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2742_, v_traces_2817_);
lean_dec_ref(v_traces_2817_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2821_);
v___x_2823_ = v___x_2819_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2821_);
lean_ctor_set_uint64(v_reuseFailAlloc_2829_, sizeof(void*)*1, v_tid_2816_);
v___x_2823_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 4, v___x_2823_);
v___x_2825_ = v___x_2814_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_env_2805_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_nextMacroScope_2806_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_ngen_2807_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_auxDeclNGen_2808_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v___x_2823_);
lean_ctor_set(v_reuseFailAlloc_2828_, 5, v_cache_2809_);
lean_ctor_set(v_reuseFailAlloc_2828_, 6, v_messages_2810_);
lean_ctor_set(v_reuseFailAlloc_2828_, 7, v_infoState_2811_);
lean_ctor_set(v_reuseFailAlloc_2828_, 8, v_snapshotTasks_2812_);
v___x_2825_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_st_ref_set(v___y_2748_, v___x_2825_);
v___x_2827_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_2750_);
return v___x_2827_;
}
}
}
}
}
else
{
goto v___jp_2796_;
}
}
else
{
goto v___jp_2796_;
}
}
v___jp_2832_:
{
double v___x_2834_; double v___x_2835_; double v___x_2836_; uint8_t v___x_2837_; 
v___x_2834_ = lean_unbox_float(v_snd_2770_);
v___x_2835_ = lean_unbox_float(v_fst_2769_);
v___x_2836_ = lean_float_sub(v___x_2834_, v___x_2835_);
v___x_2837_ = lean_float_decLt(v___y_2833_, v___x_2836_);
v___y_2802_ = v___x_2837_;
goto v___jp_2801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2850_, lean_object* v_collapsed_2851_, lean_object* v_tag_2852_, lean_object* v_opts_2853_, lean_object* v_clsEnabled_2854_, lean_object* v_oldTraces_2855_, lean_object* v_msg_2856_, lean_object* v_resStartStop_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
uint8_t v_collapsed_boxed_2863_; uint8_t v_clsEnabled_boxed_2864_; lean_object* v_res_2865_; 
v_collapsed_boxed_2863_ = lean_unbox(v_collapsed_2851_);
v_clsEnabled_boxed_2864_ = lean_unbox(v_clsEnabled_2854_);
v_res_2865_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2850_, v_collapsed_boxed_2863_, v_tag_2852_, v_opts_2853_, v_clsEnabled_boxed_2864_, v_oldTraces_2855_, v_msg_2856_, v_resStartStop_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec_ref(v_opts_2853_);
return v_res_2865_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2868_ = l_Lean_stringToMessageData(v___x_2867_);
return v___x_2868_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2871_ = l_Lean_stringToMessageData(v___x_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2872_, lean_object* v_type_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_options_2879_; lean_object* v_inheritedTraceOptions_2880_; uint8_t v_hasTrace_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___f_2888_; lean_object* v___x_2889_; lean_object* v___f_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
v_options_2879_ = lean_ctor_get(v_a_2876_, 2);
v_inheritedTraceOptions_2880_ = lean_ctor_get(v_a_2876_, 13);
v_hasTrace_2881_ = lean_ctor_get_uint8(v_options_2879_, sizeof(void*)*1);
v___x_2882_ = 0;
lean_inc(v_declName_2872_);
v___x_2883_ = l_Lean_MessageData_ofConstName(v_declName_2872_, v___x_2882_);
v___x_2884_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1);
v___x_2885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2884_);
lean_ctor_set(v___x_2885_, 1, v___x_2883_);
v___x_2886_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3);
v___x_2887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2886_);
v___f_2888_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 2, 1);
lean_closure_set(v___f_2888_, 0, v___x_2887_);
v___x_2889_ = lean_box(0);
lean_inc_ref(v_type_2873_);
v___f_2890_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2890_, 0, v_type_2873_);
lean_closure_set(v___f_2890_, 1, v___x_2889_);
lean_closure_set(v___f_2890_, 2, v_declName_2872_);
v___x_2891_ = lean_box(v___x_2882_);
v___x_2892_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2892_, 0, lean_box(0));
lean_closure_set(v___x_2892_, 1, v___f_2890_);
lean_closure_set(v___x_2892_, 2, v___x_2891_);
if (v_hasTrace_2881_ == 0)
{
lean_object* v___x_2893_; 
lean_dec_ref(v_type_2873_);
v___x_2893_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2892_, v___f_2888_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
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
v_reuseFailAlloc_2900_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
v_a_2902_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2893_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2893_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v___f_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; uint8_t v___x_2914_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v_a_2918_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v_a_2933_; 
v___f_2910_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2910_, 0, v_type_2873_);
v___x_2911_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_2912_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2913_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2914_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2880_, v_options_2879_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = l_Lean_trace_profiler;
v___x_2984_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2879_, v___x_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
lean_dec_ref(v___f_2910_);
v___x_2985_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2892_, v___f_2888_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
v_a_2994_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2985_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2985_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
goto v___jp_2942_;
}
}
else
{
goto v___jp_2942_;
}
v___jp_2915_:
{
lean_object* v___x_2919_; double v___x_2920_; double v___x_2921_; double v___x_2922_; double v___x_2923_; double v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2919_ = lean_io_mono_nanos_now();
v___x_2920_ = lean_float_of_nat(v___y_2917_);
v___x_2921_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2922_ = lean_float_div(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_float_of_nat(v___x_2919_);
v___x_2924_ = lean_float_div(v___x_2923_, v___x_2921_);
v___x_2925_ = lean_box_float(v___x_2922_);
v___x_2926_ = lean_box_float(v___x_2924_);
v___x_2927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2925_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v_a_2918_);
lean_ctor_set(v___x_2928_, 1, v___x_2927_);
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2911_, v_hasTrace_2881_, v___x_2912_, v_options_2879_, v___x_2914_, v___y_2916_, v___f_2910_, v___x_2928_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2929_;
}
v___jp_2930_:
{
lean_object* v___x_2934_; double v___x_2935_; double v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2934_ = lean_io_get_num_heartbeats();
v___x_2935_ = lean_float_of_nat(v___y_2932_);
v___x_2936_ = lean_float_of_nat(v___x_2934_);
v___x_2937_ = lean_box_float(v___x_2935_);
v___x_2938_ = lean_box_float(v___x_2936_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v_a_2933_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2911_, v_hasTrace_2881_, v___x_2912_, v_options_2879_, v___x_2914_, v___y_2931_, v___f_2910_, v___x_2940_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
return v___x_2941_;
}
v___jp_2942_:
{
lean_object* v___x_2943_; lean_object* v_a_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2943_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2877_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2946_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2879_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_io_mono_nanos_now();
v___x_2948_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2892_, v___f_2888_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set_tag(v___x_2951_, 1);
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
v___y_2916_ = v_a_2944_;
v___y_2917_ = v___x_2947_;
v_a_2918_ = v___x_2954_;
goto v___jp_2915_;
}
}
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
v_a_2957_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2948_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2948_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
lean_ctor_set_tag(v___x_2959_, 0);
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
v___y_2916_ = v_a_2944_;
v___y_2917_ = v___x_2947_;
v_a_2918_ = v___x_2962_;
goto v___jp_2915_;
}
}
}
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = lean_io_get_num_heartbeats();
v___x_2966_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2892_, v___f_2888_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2966_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2966_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 1);
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
v___y_2931_ = v_a_2944_;
v___y_2932_ = v___x_2965_;
v_a_2933_ = v___x_2972_;
goto v___jp_2930_;
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
v_a_2975_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2966_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2966_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 0);
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
v___y_2931_ = v_a_2944_;
v___y_2932_ = v___x_2965_;
v_a_2933_ = v___x_2980_;
goto v___jp_2930_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed(lean_object* v_declName_3002_, lean_object* v_type_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(v_declName_3002_, v_type_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
lean_dec_ref(v_a_3004_);
return v_res_3009_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(lean_object* v_env_3010_, lean_object* v_n_3011_, lean_object* v_x_3012_){
_start:
{
uint8_t v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3013_ = 1;
v___x_3014_ = l_Lean_Environment_setExporting(v_env_3010_, v___x_3013_);
v___x_3015_ = 0;
v___x_3016_ = l_Lean_Environment_find_x3f(v___x_3014_, v_n_3011_, v___x_3015_);
if (lean_obj_tag(v___x_3016_) == 0)
{
return v___x_3015_;
}
else
{
lean_object* v_val_3017_; uint8_t v___x_3018_; 
v_val_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_val_3017_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = l_Lean_ConstantInfo_hasValue(v_val_3017_, v___x_3015_);
lean_dec(v_val_3017_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed(lean_object* v_env_3019_, lean_object* v_n_3020_, lean_object* v_x_3021_){
_start:
{
uint8_t v_res_3022_; lean_object* v_r_3023_; 
v_res_3022_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(v_env_3019_, v_n_3020_, v_x_3021_);
lean_dec_ref(v_x_3021_);
v_r_3023_ = lean_box(v_res_3022_);
return v_r_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3024_, lean_object* v_x_3025_){
_start:
{
if (lean_obj_tag(v_x_3025_) == 0)
{
lean_object* v_k_3026_; lean_object* v_v_3027_; lean_object* v_l_3028_; lean_object* v_r_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v_k_3026_ = lean_ctor_get(v_x_3025_, 1);
v_v_3027_ = lean_ctor_get(v_x_3025_, 2);
v_l_3028_ = lean_ctor_get(v_x_3025_, 3);
v_r_3029_ = lean_ctor_get(v_x_3025_, 4);
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_3024_, v_l_3028_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3034_, lean_object* v_x_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_3034_, v_x_3035_);
lean_dec(v_x_3035_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(lean_object* v_env_3039_, lean_object* v_s_3040_){
_start:
{
lean_object* v___f_3041_; lean_object* v___x_3042_; lean_object* v_all_3043_; lean_object* v___x_3044_; lean_object* v_exported_3045_; lean_object* v___x_3046_; 
v___f_3041_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3041_, 0, v_env_3039_);
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v_all_3043_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_3042_, v_s_3040_);
v___x_3044_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3041_, v_s_3040_);
v_exported_3045_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_3042_, v___x_3044_);
lean_dec(v___x_3044_);
lean_inc_ref(v_exported_3045_);
v___x_3046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3046_, 0, v_exported_3045_);
lean_ctor_set(v___x_3046_, 1, v_exported_3045_);
lean_ctor_set(v___x_3046_, 2, v_all_3043_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___f_3059_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v___x_3062_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3060_, v___x_3061_, v___f_3059_);
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed(lean_object* v_a_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_();
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0(lean_object* v_init_3065_, lean_object* v_t_3066_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_3065_, v_t_3066_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3068_, lean_object* v_t_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0(v_init_3068_, v_t_3069_);
lean_dec(v_t_3069_);
return v_res_3070_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3071_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
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
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3118_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3117_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3117_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v_env_3092_; lean_object* v_nextMacroScope_3093_; lean_object* v_ngen_3094_; lean_object* v_auxDeclNGen_3095_; lean_object* v_traceState_3096_; lean_object* v_messages_3097_; lean_object* v_infoState_3098_; lean_object* v_snapshotTasks_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3115_; 
v___x_3091_ = lean_st_ref_take(v_a_3081_);
v_env_3092_ = lean_ctor_get(v___x_3091_, 0);
v_nextMacroScope_3093_ = lean_ctor_get(v___x_3091_, 1);
v_ngen_3094_ = lean_ctor_get(v___x_3091_, 2);
v_auxDeclNGen_3095_ = lean_ctor_get(v___x_3091_, 3);
v_traceState_3096_ = lean_ctor_get(v___x_3091_, 4);
v_messages_3097_ = lean_ctor_get(v___x_3091_, 6);
v_infoState_3098_ = lean_ctor_get(v___x_3091_, 7);
v_snapshotTasks_3099_ = lean_ctor_get(v___x_3091_, 8);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3091_, 5);
lean_dec(v_unused_3116_);
v___x_3101_ = v___x_3091_;
v_isShared_3102_ = v_isSharedCheck_3115_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snapshotTasks_3099_);
lean_inc(v_infoState_3098_);
lean_inc(v_messages_3097_);
lean_inc(v_traceState_3096_);
lean_inc(v_auxDeclNGen_3095_);
lean_inc(v_ngen_3094_);
lean_inc(v_nextMacroScope_3093_);
lean_inc(v_env_3092_);
lean_dec(v___x_3091_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3115_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3103_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3084_);
v___x_3104_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3104_, 0, v_declName_3084_);
lean_ctor_set(v___x_3104_, 1, v_levelParams_3083_);
lean_ctor_set(v___x_3104_, 2, v_type_3085_);
lean_ctor_set(v___x_3104_, 3, v_value_3086_);
lean_ctor_set(v___x_3104_, 4, v_recArgPos_3078_);
lean_ctor_set(v___x_3104_, 5, v_declNames_3077_);
lean_ctor_set(v___x_3104_, 6, v_fixedParamPerms_3079_);
v___x_3105_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3103_, v_env_3092_, v_declName_3084_, v___x_3104_);
v___x_3106_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 5, v___x_3106_);
lean_ctor_set(v___x_3101_, 0, v___x_3105_);
v___x_3108_ = v___x_3101_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_nextMacroScope_3093_);
lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_ngen_3094_);
lean_ctor_set(v_reuseFailAlloc_3114_, 3, v_auxDeclNGen_3095_);
lean_ctor_set(v_reuseFailAlloc_3114_, 4, v_traceState_3096_);
lean_ctor_set(v_reuseFailAlloc_3114_, 5, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3114_, 6, v_messages_3097_);
lean_ctor_set(v_reuseFailAlloc_3114_, 7, v_infoState_3098_);
lean_ctor_set(v_reuseFailAlloc_3114_, 8, v_snapshotTasks_3099_);
v___x_3108_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3109_ = lean_st_ref_set(v_a_3081_, v___x_3108_);
v___x_3110_ = lean_box(0);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3110_);
v___x_3112_ = v___x_3089_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3119_, lean_object* v_declNames_3120_, lean_object* v_recArgPos_3121_, lean_object* v_fixedParamPerms_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3119_, v_declNames_3120_, v_recArgPos_3121_, v_fixedParamPerms_3122_, v_a_3123_, v_a_3124_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3127_, lean_object* v_k_3128_, uint8_t v_cleanupAnnotations_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___f_3135_; uint8_t v___x_3136_; uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___f_3135_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3135_, 0, v_k_3128_);
v___x_3136_ = 1;
v___x_3137_ = 0;
v___x_3138_ = lean_box(0);
v___x_3139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3127_, v___x_3136_, v___x_3137_, v___x_3136_, v___x_3137_, v___x_3138_, v___f_3135_, v_cleanupAnnotations_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
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
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3139_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3139_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3156_, lean_object* v_k_3157_, lean_object* v_cleanupAnnotations_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3164_; lean_object* v_res_3165_; 
v_cleanupAnnotations_boxed_3164_ = lean_unbox(v_cleanupAnnotations_3158_);
v_res_3165_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3156_, v_k_3157_, v_cleanupAnnotations_boxed_3164_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3166_, lean_object* v_e_3167_, lean_object* v_k_3168_, uint8_t v_cleanupAnnotations_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; 
v___x_3175_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3167_, v_k_3168_, v_cleanupAnnotations_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3176_, lean_object* v_e_3177_, lean_object* v_k_3178_, lean_object* v_cleanupAnnotations_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3185_; lean_object* v_res_3186_; 
v_cleanupAnnotations_boxed_3185_ = lean_unbox(v_cleanupAnnotations_3179_);
v_res_3186_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3176_, v_e_3177_, v_k_3178_, v_cleanupAnnotations_boxed_3185_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3187_, uint8_t v_isExporting_3188_, lean_object* v___x_3189_, lean_object* v___y_3190_, lean_object* v___x_3191_, lean_object* v_a_x3f_3192_){
_start:
{
lean_object* v___x_3194_; lean_object* v_env_3195_; lean_object* v_nextMacroScope_3196_; lean_object* v_ngen_3197_; lean_object* v_auxDeclNGen_3198_; lean_object* v_traceState_3199_; lean_object* v_messages_3200_; lean_object* v_infoState_3201_; lean_object* v_snapshotTasks_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3227_; 
v___x_3194_ = lean_st_ref_take(v___y_3187_);
v_env_3195_ = lean_ctor_get(v___x_3194_, 0);
v_nextMacroScope_3196_ = lean_ctor_get(v___x_3194_, 1);
v_ngen_3197_ = lean_ctor_get(v___x_3194_, 2);
v_auxDeclNGen_3198_ = lean_ctor_get(v___x_3194_, 3);
v_traceState_3199_ = lean_ctor_get(v___x_3194_, 4);
v_messages_3200_ = lean_ctor_get(v___x_3194_, 6);
v_infoState_3201_ = lean_ctor_get(v___x_3194_, 7);
v_snapshotTasks_3202_ = lean_ctor_get(v___x_3194_, 8);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3194_, 5);
lean_dec(v_unused_3228_);
v___x_3204_ = v___x_3194_;
v_isShared_3205_ = v_isSharedCheck_3227_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_snapshotTasks_3202_);
lean_inc(v_infoState_3201_);
lean_inc(v_messages_3200_);
lean_inc(v_traceState_3199_);
lean_inc(v_auxDeclNGen_3198_);
lean_inc(v_ngen_3197_);
lean_inc(v_nextMacroScope_3196_);
lean_inc(v_env_3195_);
lean_dec(v___x_3194_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3227_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3208_; 
v___x_3206_ = l_Lean_Environment_setExporting(v_env_3195_, v_isExporting_3188_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 5, v___x_3189_);
lean_ctor_set(v___x_3204_, 0, v___x_3206_);
v___x_3208_ = v___x_3204_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3226_, 1, v_nextMacroScope_3196_);
lean_ctor_set(v_reuseFailAlloc_3226_, 2, v_ngen_3197_);
lean_ctor_set(v_reuseFailAlloc_3226_, 3, v_auxDeclNGen_3198_);
lean_ctor_set(v_reuseFailAlloc_3226_, 4, v_traceState_3199_);
lean_ctor_set(v_reuseFailAlloc_3226_, 5, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3226_, 6, v_messages_3200_);
lean_ctor_set(v_reuseFailAlloc_3226_, 7, v_infoState_3201_);
lean_ctor_set(v_reuseFailAlloc_3226_, 8, v_snapshotTasks_3202_);
v___x_3208_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v_mctx_3211_; lean_object* v_zetaDeltaFVarIds_3212_; lean_object* v_postponed_3213_; lean_object* v_diag_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3224_; 
v___x_3209_ = lean_st_ref_set(v___y_3187_, v___x_3208_);
v___x_3210_ = lean_st_ref_take(v___y_3190_);
v_mctx_3211_ = lean_ctor_get(v___x_3210_, 0);
v_zetaDeltaFVarIds_3212_ = lean_ctor_get(v___x_3210_, 2);
v_postponed_3213_ = lean_ctor_get(v___x_3210_, 3);
v_diag_3214_ = lean_ctor_get(v___x_3210_, 4);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3224_ == 0)
{
lean_object* v_unused_3225_; 
v_unused_3225_ = lean_ctor_get(v___x_3210_, 1);
lean_dec(v_unused_3225_);
v___x_3216_ = v___x_3210_;
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_diag_3214_);
lean_inc(v_postponed_3213_);
lean_inc(v_zetaDeltaFVarIds_3212_);
lean_inc(v_mctx_3211_);
lean_dec(v___x_3210_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 1, v___x_3191_);
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_mctx_3211_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3223_, 2, v_zetaDeltaFVarIds_3212_);
lean_ctor_set(v_reuseFailAlloc_3223_, 3, v_postponed_3213_);
lean_ctor_set(v_reuseFailAlloc_3223_, 4, v_diag_3214_);
v___x_3219_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3220_ = lean_st_ref_set(v___y_3190_, v___x_3219_);
v___x_3221_ = lean_box(0);
v___x_3222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
return v___x_3222_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3229_, lean_object* v_isExporting_3230_, lean_object* v___x_3231_, lean_object* v___y_3232_, lean_object* v___x_3233_, lean_object* v_a_x3f_3234_, lean_object* v___y_3235_){
_start:
{
uint8_t v_isExporting_boxed_3236_; lean_object* v_res_3237_; 
v_isExporting_boxed_3236_ = lean_unbox(v_isExporting_3230_);
v_res_3237_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3229_, v_isExporting_boxed_3236_, v___x_3231_, v___y_3232_, v___x_3233_, v_a_x3f_3234_);
lean_dec(v_a_x3f_3234_);
lean_dec(v___y_3232_);
lean_dec(v___y_3229_);
return v_res_3237_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3239_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
lean_ctor_set(v___x_3239_, 2, v___x_3238_);
lean_ctor_set(v___x_3239_, 3, v___x_3238_);
lean_ctor_set(v___x_3239_, 4, v___x_3238_);
lean_ctor_set(v___x_3239_, 5, v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3240_, uint8_t v_isExporting_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; lean_object* v_env_3248_; uint8_t v_isExporting_3249_; lean_object* v___x_3250_; lean_object* v_env_3251_; lean_object* v_nextMacroScope_3252_; lean_object* v_ngen_3253_; lean_object* v_auxDeclNGen_3254_; lean_object* v_traceState_3255_; lean_object* v_messages_3256_; lean_object* v_infoState_3257_; lean_object* v_snapshotTasks_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3312_; 
v___x_3247_ = lean_st_ref_get(v___y_3245_);
v_env_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_env_3248_);
lean_dec(v___x_3247_);
v_isExporting_3249_ = lean_ctor_get_uint8(v_env_3248_, sizeof(void*)*8);
lean_dec_ref(v_env_3248_);
v___x_3250_ = lean_st_ref_take(v___y_3245_);
v_env_3251_ = lean_ctor_get(v___x_3250_, 0);
v_nextMacroScope_3252_ = lean_ctor_get(v___x_3250_, 1);
v_ngen_3253_ = lean_ctor_get(v___x_3250_, 2);
v_auxDeclNGen_3254_ = lean_ctor_get(v___x_3250_, 3);
v_traceState_3255_ = lean_ctor_get(v___x_3250_, 4);
v_messages_3256_ = lean_ctor_get(v___x_3250_, 6);
v_infoState_3257_ = lean_ctor_get(v___x_3250_, 7);
v_snapshotTasks_3258_ = lean_ctor_get(v___x_3250_, 8);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3312_ == 0)
{
lean_object* v_unused_3313_; 
v_unused_3313_ = lean_ctor_get(v___x_3250_, 5);
lean_dec(v_unused_3313_);
v___x_3260_ = v___x_3250_;
v_isShared_3261_ = v_isSharedCheck_3312_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_snapshotTasks_3258_);
lean_inc(v_infoState_3257_);
lean_inc(v_messages_3256_);
lean_inc(v_traceState_3255_);
lean_inc(v_auxDeclNGen_3254_);
lean_inc(v_ngen_3253_);
lean_inc(v_nextMacroScope_3252_);
lean_inc(v_env_3251_);
lean_dec(v___x_3250_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3312_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3265_; 
v___x_3262_ = l_Lean_Environment_setExporting(v_env_3251_, v_isExporting_3241_);
v___x_3263_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3261_ == 0)
{
lean_ctor_set(v___x_3260_, 5, v___x_3263_);
lean_ctor_set(v___x_3260_, 0, v___x_3262_);
v___x_3265_ = v___x_3260_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3262_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_nextMacroScope_3252_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v_ngen_3253_);
lean_ctor_set(v_reuseFailAlloc_3311_, 3, v_auxDeclNGen_3254_);
lean_ctor_set(v_reuseFailAlloc_3311_, 4, v_traceState_3255_);
lean_ctor_set(v_reuseFailAlloc_3311_, 5, v___x_3263_);
lean_ctor_set(v_reuseFailAlloc_3311_, 6, v_messages_3256_);
lean_ctor_set(v_reuseFailAlloc_3311_, 7, v_infoState_3257_);
lean_ctor_set(v_reuseFailAlloc_3311_, 8, v_snapshotTasks_3258_);
v___x_3265_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v_mctx_3268_; lean_object* v_zetaDeltaFVarIds_3269_; lean_object* v_postponed_3270_; lean_object* v_diag_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3309_; 
v___x_3266_ = lean_st_ref_set(v___y_3245_, v___x_3265_);
v___x_3267_ = lean_st_ref_take(v___y_3243_);
v_mctx_3268_ = lean_ctor_get(v___x_3267_, 0);
v_zetaDeltaFVarIds_3269_ = lean_ctor_get(v___x_3267_, 2);
v_postponed_3270_ = lean_ctor_get(v___x_3267_, 3);
v_diag_3271_ = lean_ctor_get(v___x_3267_, 4);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3309_ == 0)
{
lean_object* v_unused_3310_; 
v_unused_3310_ = lean_ctor_get(v___x_3267_, 1);
lean_dec(v_unused_3310_);
v___x_3273_ = v___x_3267_;
v_isShared_3274_ = v_isSharedCheck_3309_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_diag_3271_);
lean_inc(v_postponed_3270_);
lean_inc(v_zetaDeltaFVarIds_3269_);
lean_inc(v_mctx_3268_);
lean_dec(v___x_3267_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3309_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3277_; 
v___x_3275_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 1, v___x_3275_);
v___x_3277_ = v___x_3273_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_mctx_3268_);
lean_ctor_set(v_reuseFailAlloc_3308_, 1, v___x_3275_);
lean_ctor_set(v_reuseFailAlloc_3308_, 2, v_zetaDeltaFVarIds_3269_);
lean_ctor_set(v_reuseFailAlloc_3308_, 3, v_postponed_3270_);
lean_ctor_set(v_reuseFailAlloc_3308_, 4, v_diag_3271_);
v___x_3277_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3278_; lean_object* v_r_3279_; 
v___x_3278_ = lean_st_ref_set(v___y_3243_, v___x_3277_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
v_r_3279_ = lean_apply_5(v_x_3240_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, lean_box(0));
if (lean_obj_tag(v_r_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3296_; 
v_a_3280_ = lean_ctor_get(v_r_3279_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_r_3279_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3282_ = v_r_3279_;
v_isShared_3283_ = v_isSharedCheck_3296_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v_r_3279_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3296_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
lean_inc(v_a_3280_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set_tag(v___x_3282_, 1);
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
lean_object* v___x_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
v___x_3286_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3245_, v_isExporting_3249_, v___x_3263_, v___y_3243_, v___x_3275_, v___x_3285_);
lean_dec_ref(v___x_3285_);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v___x_3286_, 0);
lean_dec(v_unused_3294_);
v___x_3288_ = v___x_3286_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_dec(v___x_3286_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v_a_3280_);
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3280_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
v_a_3297_ = lean_ctor_get(v_r_3279_, 0);
lean_inc(v_a_3297_);
lean_dec_ref(v_r_3279_);
v___x_3298_ = lean_box(0);
v___x_3299_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3245_, v_isExporting_3249_, v___x_3263_, v___y_3243_, v___x_3275_, v___x_3298_);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3306_ == 0)
{
lean_object* v_unused_3307_; 
v_unused_3307_ = lean_ctor_get(v___x_3299_, 0);
lean_dec(v_unused_3307_);
v___x_3301_ = v___x_3299_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_dec(v___x_3299_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
lean_ctor_set_tag(v___x_3301_, 1);
lean_ctor_set(v___x_3301_, 0, v_a_3297_);
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3297_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3314_, lean_object* v_isExporting_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
uint8_t v_isExporting_boxed_3321_; lean_object* v_res_3322_; 
v_isExporting_boxed_3321_ = lean_unbox(v_isExporting_3315_);
v_res_3322_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3314_, v_isExporting_boxed_3321_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
lean_dec(v___y_3317_);
lean_dec_ref(v___y_3316_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3323_, uint8_t v_when_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
if (v_when_3324_ == 0)
{
lean_object* v___x_3330_; 
lean_inc(v___y_3328_);
lean_inc_ref(v___y_3327_);
lean_inc(v___y_3326_);
lean_inc_ref(v___y_3325_);
v___x_3330_ = lean_apply_5(v_x_3323_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, lean_box(0));
return v___x_3330_;
}
else
{
uint8_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = 0;
v___x_3332_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3323_, v___x_3331_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3333_, lean_object* v_when_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v_when_boxed_3340_; lean_object* v_res_3341_; 
v_when_boxed_3340_ = lean_unbox(v_when_3334_);
v_res_3341_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3333_, v_when_boxed_3340_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
if (lean_obj_tag(v_a_3342_) == 0)
{
lean_object* v___x_3344_; 
v___x_3344_ = l_List_reverse___redArg(v_a_3343_);
return v___x_3344_;
}
else
{
lean_object* v_head_3345_; lean_object* v_tail_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3355_; 
v_head_3345_ = lean_ctor_get(v_a_3342_, 0);
v_tail_3346_ = lean_ctor_get(v_a_3342_, 1);
v_isSharedCheck_3355_ = !lean_is_exclusive(v_a_3342_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3348_ = v_a_3342_;
v_isShared_3349_ = v_isSharedCheck_3355_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_tail_3346_);
lean_inc(v_head_3345_);
lean_dec(v_a_3342_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3355_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3352_; 
v___x_3350_ = l_Lean_mkLevelParam(v_head_3345_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 1, v_a_3343_);
lean_ctor_set(v___x_3348_, 0, v___x_3350_);
v___x_3352_ = v___x_3348_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3350_);
lean_ctor_set(v_reuseFailAlloc_3354_, 1, v_a_3343_);
v___x_3352_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
v_a_3342_ = v_tail_3346_;
v_a_3343_ = v___x_3352_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3356_, lean_object* v_declName_3357_, lean_object* v_name_3358_, lean_object* v_xs_3359_, lean_object* v_body_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; lean_object* v_us_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3366_ = lean_box(0);
lean_inc(v_levelParams_3356_);
v_us_3367_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3356_, v___x_3366_);
lean_inc(v_declName_3357_);
v___x_3368_ = l_Lean_mkConst(v_declName_3357_, v_us_3367_);
v___x_3369_ = l_Lean_mkAppN(v___x_3368_, v_xs_3359_);
v___x_3370_ = l_Lean_Meta_mkEq(v___x_3369_, v_body_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc_n(v_a_3371_, 2);
lean_dec_ref(v___x_3370_);
v___x_3372_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3372_, 0, v_declName_3357_);
lean_closure_set(v___x_3372_, 1, v_a_3371_);
v___x_3373_ = 1;
v___x_3374_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3372_, v___x_3373_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; uint8_t v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref(v___x_3374_);
v___x_3376_ = 0;
v___x_3377_ = 1;
v___x_3378_ = l_Lean_Meta_mkForallFVars(v_xs_3359_, v_a_3371_, v___x_3376_, v___x_3373_, v___x_3373_, v___x_3377_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = l_Lean_Meta_letToHave(v_a_3379_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref(v___x_3380_);
v___x_3382_ = l_Lean_Meta_mkLambdaFVars(v_xs_3359_, v_a_3375_, v___x_3376_, v___x_3373_, v___x_3376_, v___x_3373_, v___x_3377_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
lean_inc_n(v_name_3358_, 2);
v___x_3384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3384_, 0, v_name_3358_);
lean_ctor_set(v___x_3384_, 1, v_levelParams_3356_);
lean_ctor_set(v___x_3384_, 2, v_a_3381_);
v___x_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3385_, 0, v_name_3358_);
lean_ctor_set(v___x_3385_, 1, v___x_3366_);
v___x_3386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set(v___x_3386_, 1, v_a_3383_);
lean_ctor_set(v___x_3386_, 2, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
v___x_3388_ = l_Lean_addDecl(v___x_3387_, v___x_3376_, v___y_3363_, v___y_3364_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v___x_3389_; 
lean_dec_ref(v___x_3388_);
v___x_3389_ = l_Lean_inferDefEqAttr(v_name_3358_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
return v___x_3389_;
}
else
{
lean_dec(v_name_3358_);
return v___x_3388_;
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v_a_3381_);
lean_dec(v_name_3358_);
lean_dec(v_levelParams_3356_);
v_a_3390_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3382_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3382_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_a_3375_);
lean_dec(v_name_3358_);
lean_dec(v_levelParams_3356_);
v_a_3398_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3380_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3380_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_a_3375_);
lean_dec(v_name_3358_);
lean_dec(v_levelParams_3356_);
v_a_3406_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3378_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3378_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec(v_a_3371_);
lean_dec(v_name_3358_);
lean_dec(v_levelParams_3356_);
v_a_3414_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3374_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3374_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3429_; 
lean_dec(v_name_3358_);
lean_dec(v_declName_3357_);
lean_dec(v_levelParams_3356_);
v_a_3422_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3370_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3370_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3430_, lean_object* v_declName_3431_, lean_object* v_name_3432_, lean_object* v_xs_3433_, lean_object* v_body_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3430_, v_declName_3431_, v_name_3432_, v_xs_3433_, v_body_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec_ref(v_xs_3433_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3441_, lean_object* v_k_3442_, uint8_t v_v_3443_){
_start:
{
lean_object* v_map_3444_; uint8_t v_hasTrace_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3459_; 
v_map_3444_ = lean_ctor_get(v_o_3441_, 0);
v_hasTrace_3445_ = lean_ctor_get_uint8(v_o_3441_, sizeof(void*)*1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_o_3441_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3447_ = v_o_3441_;
v_isShared_3448_ = v_isSharedCheck_3459_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_map_3444_);
lean_dec(v_o_3441_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3459_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3449_, 0, v_v_3443_);
lean_inc(v_k_3442_);
v___x_3450_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3442_, v___x_3449_, v_map_3444_);
if (v_hasTrace_3445_ == 0)
{
lean_object* v___x_3451_; uint8_t v___x_3452_; lean_object* v___x_3454_; 
v___x_3451_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3452_ = l_Lean_Name_isPrefixOf(v___x_3451_, v_k_3442_);
lean_dec(v_k_3442_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3450_);
v___x_3454_ = v___x_3447_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3450_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
lean_ctor_set_uint8(v___x_3454_, sizeof(void*)*1, v___x_3452_);
return v___x_3454_;
}
}
else
{
lean_object* v___x_3457_; 
lean_dec(v_k_3442_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3450_);
v___x_3457_ = v___x_3447_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3450_);
lean_ctor_set_uint8(v_reuseFailAlloc_3458_, sizeof(void*)*1, v_hasTrace_3445_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3460_, lean_object* v_k_3461_, lean_object* v_v_3462_){
_start:
{
uint8_t v_v_boxed_3463_; lean_object* v_res_3464_; 
v_v_boxed_3463_ = lean_unbox(v_v_3462_);
v_res_3464_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3460_, v_k_3461_, v_v_boxed_3463_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3465_, lean_object* v_opt_3466_, uint8_t v_val_3467_){
_start:
{
lean_object* v_name_3468_; lean_object* v___x_3469_; 
v_name_3468_ = lean_ctor_get(v_opt_3466_, 0);
lean_inc(v_name_3468_);
lean_dec_ref(v_opt_3466_);
v___x_3469_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3465_, v_name_3468_, v_val_3467_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3470_, lean_object* v_opt_3471_, lean_object* v_val_3472_){
_start:
{
uint8_t v_val_boxed_3473_; lean_object* v_res_3474_; 
v_val_boxed_3473_ = lean_unbox(v_val_3472_);
v_res_3474_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3470_, v_opt_3471_, v_val_boxed_3473_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3475_, lean_object* v_info_3476_, lean_object* v_name_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v___x_3483_; lean_object* v_levelParams_3484_; lean_object* v_value_3485_; lean_object* v_fileName_3486_; lean_object* v_fileMap_3487_; lean_object* v_options_3488_; lean_object* v_currRecDepth_3489_; lean_object* v_ref_3490_; lean_object* v_currNamespace_3491_; lean_object* v_openDecls_3492_; lean_object* v_initHeartbeats_3493_; lean_object* v_maxHeartbeats_3494_; lean_object* v_quotContext_3495_; lean_object* v_currMacroScope_3496_; lean_object* v_cancelTk_x3f_3497_; uint8_t v_suppressElabErrors_3498_; lean_object* v_inheritedTraceOptions_3499_; lean_object* v_env_3500_; lean_object* v___f_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; lean_object* v_fileName_3508_; lean_object* v_fileMap_3509_; lean_object* v_currRecDepth_3510_; lean_object* v_ref_3511_; lean_object* v_currNamespace_3512_; lean_object* v_openDecls_3513_; lean_object* v_initHeartbeats_3514_; lean_object* v_maxHeartbeats_3515_; lean_object* v_quotContext_3516_; lean_object* v_currMacroScope_3517_; lean_object* v_cancelTk_x3f_3518_; uint8_t v_suppressElabErrors_3519_; lean_object* v_inheritedTraceOptions_3520_; lean_object* v___y_3521_; uint8_t v___y_3527_; uint8_t v___x_3548_; 
v___x_3483_ = lean_st_ref_get(v_a_3481_);
v_levelParams_3484_ = lean_ctor_get(v_info_3476_, 1);
lean_inc(v_levelParams_3484_);
v_value_3485_ = lean_ctor_get(v_info_3476_, 3);
lean_inc_ref(v_value_3485_);
lean_dec_ref(v_info_3476_);
v_fileName_3486_ = lean_ctor_get(v_a_3480_, 0);
v_fileMap_3487_ = lean_ctor_get(v_a_3480_, 1);
v_options_3488_ = lean_ctor_get(v_a_3480_, 2);
v_currRecDepth_3489_ = lean_ctor_get(v_a_3480_, 3);
v_ref_3490_ = lean_ctor_get(v_a_3480_, 5);
v_currNamespace_3491_ = lean_ctor_get(v_a_3480_, 6);
v_openDecls_3492_ = lean_ctor_get(v_a_3480_, 7);
v_initHeartbeats_3493_ = lean_ctor_get(v_a_3480_, 8);
v_maxHeartbeats_3494_ = lean_ctor_get(v_a_3480_, 9);
v_quotContext_3495_ = lean_ctor_get(v_a_3480_, 10);
v_currMacroScope_3496_ = lean_ctor_get(v_a_3480_, 11);
v_cancelTk_x3f_3497_ = lean_ctor_get(v_a_3480_, 12);
v_suppressElabErrors_3498_ = lean_ctor_get_uint8(v_a_3480_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3499_ = lean_ctor_get(v_a_3480_, 13);
v_env_3500_ = lean_ctor_get(v___x_3483_, 0);
lean_inc_ref(v_env_3500_);
lean_dec(v___x_3483_);
v___f_3501_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3501_, 0, v_levelParams_3484_);
lean_closure_set(v___f_3501_, 1, v_declName_3475_);
lean_closure_set(v___f_3501_, 2, v_name_3477_);
v___x_3502_ = 0;
v___x_3503_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3488_);
v___x_3504_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3488_, v___x_3503_, v___x_3502_);
v___x_3505_ = l_Lean_diagnostics;
v___x_3506_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v___x_3504_, v___x_3505_);
v___x_3548_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3500_);
lean_dec_ref(v_env_3500_);
if (v___x_3548_ == 0)
{
if (v___x_3506_ == 0)
{
v_fileName_3508_ = v_fileName_3486_;
v_fileMap_3509_ = v_fileMap_3487_;
v_currRecDepth_3510_ = v_currRecDepth_3489_;
v_ref_3511_ = v_ref_3490_;
v_currNamespace_3512_ = v_currNamespace_3491_;
v_openDecls_3513_ = v_openDecls_3492_;
v_initHeartbeats_3514_ = v_initHeartbeats_3493_;
v_maxHeartbeats_3515_ = v_maxHeartbeats_3494_;
v_quotContext_3516_ = v_quotContext_3495_;
v_currMacroScope_3517_ = v_currMacroScope_3496_;
v_cancelTk_x3f_3518_ = v_cancelTk_x3f_3497_;
v_suppressElabErrors_3519_ = v_suppressElabErrors_3498_;
v_inheritedTraceOptions_3520_ = v_inheritedTraceOptions_3499_;
v___y_3521_ = v_a_3481_;
goto v___jp_3507_;
}
else
{
v___y_3527_ = v___x_3548_;
goto v___jp_3526_;
}
}
else
{
v___y_3527_ = v___x_3506_;
goto v___jp_3526_;
}
v___jp_3507_:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3522_ = l_Lean_maxRecDepth;
v___x_3523_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___x_3504_, v___x_3522_);
lean_inc_ref(v_inheritedTraceOptions_3520_);
lean_inc(v_cancelTk_x3f_3518_);
lean_inc(v_currMacroScope_3517_);
lean_inc(v_quotContext_3516_);
lean_inc(v_maxHeartbeats_3515_);
lean_inc(v_initHeartbeats_3514_);
lean_inc(v_openDecls_3513_);
lean_inc(v_currNamespace_3512_);
lean_inc(v_ref_3511_);
lean_inc(v_currRecDepth_3510_);
lean_inc_ref(v_fileMap_3509_);
lean_inc_ref(v_fileName_3508_);
v___x_3524_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3524_, 0, v_fileName_3508_);
lean_ctor_set(v___x_3524_, 1, v_fileMap_3509_);
lean_ctor_set(v___x_3524_, 2, v___x_3504_);
lean_ctor_set(v___x_3524_, 3, v_currRecDepth_3510_);
lean_ctor_set(v___x_3524_, 4, v___x_3523_);
lean_ctor_set(v___x_3524_, 5, v_ref_3511_);
lean_ctor_set(v___x_3524_, 6, v_currNamespace_3512_);
lean_ctor_set(v___x_3524_, 7, v_openDecls_3513_);
lean_ctor_set(v___x_3524_, 8, v_initHeartbeats_3514_);
lean_ctor_set(v___x_3524_, 9, v_maxHeartbeats_3515_);
lean_ctor_set(v___x_3524_, 10, v_quotContext_3516_);
lean_ctor_set(v___x_3524_, 11, v_currMacroScope_3517_);
lean_ctor_set(v___x_3524_, 12, v_cancelTk_x3f_3518_);
lean_ctor_set(v___x_3524_, 13, v_inheritedTraceOptions_3520_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*14, v___x_3506_);
lean_ctor_set_uint8(v___x_3524_, sizeof(void*)*14 + 1, v_suppressElabErrors_3519_);
v___x_3525_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3485_, v___f_3501_, v___x_3502_, v_a_3478_, v_a_3479_, v___x_3524_, v___y_3521_);
lean_dec_ref(v___x_3524_);
return v___x_3525_;
}
v___jp_3526_:
{
if (v___y_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v_env_3529_; lean_object* v_nextMacroScope_3530_; lean_object* v_ngen_3531_; lean_object* v_auxDeclNGen_3532_; lean_object* v_traceState_3533_; lean_object* v_messages_3534_; lean_object* v_infoState_3535_; lean_object* v_snapshotTasks_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3546_; 
v___x_3528_ = lean_st_ref_take(v_a_3481_);
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
v___x_3540_ = l_Lean_Kernel_enableDiag(v_env_3529_, v___x_3506_);
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
v___x_3544_ = lean_st_ref_set(v_a_3481_, v___x_3543_);
v_fileName_3508_ = v_fileName_3486_;
v_fileMap_3509_ = v_fileMap_3487_;
v_currRecDepth_3510_ = v_currRecDepth_3489_;
v_ref_3511_ = v_ref_3490_;
v_currNamespace_3512_ = v_currNamespace_3491_;
v_openDecls_3513_ = v_openDecls_3492_;
v_initHeartbeats_3514_ = v_initHeartbeats_3493_;
v_maxHeartbeats_3515_ = v_maxHeartbeats_3494_;
v_quotContext_3516_ = v_quotContext_3495_;
v_currMacroScope_3517_ = v_currMacroScope_3496_;
v_cancelTk_x3f_3518_ = v_cancelTk_x3f_3497_;
v_suppressElabErrors_3519_ = v_suppressElabErrors_3498_;
v_inheritedTraceOptions_3520_ = v_inheritedTraceOptions_3499_;
v___y_3521_ = v_a_3481_;
goto v___jp_3507_;
}
}
}
else
{
v_fileName_3508_ = v_fileName_3486_;
v_fileMap_3509_ = v_fileMap_3487_;
v_currRecDepth_3510_ = v_currRecDepth_3489_;
v_ref_3511_ = v_ref_3490_;
v_currNamespace_3512_ = v_currNamespace_3491_;
v_openDecls_3513_ = v_openDecls_3492_;
v_initHeartbeats_3514_ = v_initHeartbeats_3493_;
v_maxHeartbeats_3515_ = v_maxHeartbeats_3494_;
v_quotContext_3516_ = v_quotContext_3495_;
v_currMacroScope_3517_ = v_currMacroScope_3496_;
v_cancelTk_x3f_3518_ = v_cancelTk_x3f_3497_;
v_suppressElabErrors_3519_ = v_suppressElabErrors_3498_;
v_inheritedTraceOptions_3520_ = v_inheritedTraceOptions_3499_;
v___y_3521_ = v_a_3481_;
goto v___jp_3507_;
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
lean_dec_ref(v___x_3797_);
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
res = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_();
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
