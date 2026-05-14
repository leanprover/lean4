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
lean_object* v___x_773_; lean_object* v_traceState_774_; lean_object* v_traces_775_; lean_object* v___x_776_; lean_object* v_traceState_777_; lean_object* v_env_778_; lean_object* v_nextMacroScope_779_; lean_object* v_ngen_780_; lean_object* v_auxDeclNGen_781_; lean_object* v_cache_782_; lean_object* v_messages_783_; lean_object* v_infoState_784_; lean_object* v_snapshotTasks_785_; lean_object* v_newDecls_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_805_; 
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
v_newDecls_786_ = lean_ctor_get(v___x_776_, 9);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_805_ == 0)
{
v___x_788_ = v___x_776_;
v_isShared_789_ = v_isSharedCheck_805_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_newDecls_786_);
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
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_805_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint64_t v_tid_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_803_; 
v_tid_790_ = lean_ctor_get_uint64(v_traceState_777_, sizeof(void*)*1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_traceState_777_);
if (v_isSharedCheck_803_ == 0)
{
lean_object* v_unused_804_; 
v_unused_804_ = lean_ctor_get(v_traceState_777_, 0);
lean_dec(v_unused_804_);
v___x_792_ = v_traceState_777_;
v_isShared_793_ = v_isSharedCheck_803_;
goto v_resetjp_791_;
}
else
{
lean_dec(v_traceState_777_);
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
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_env_778_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_nextMacroScope_779_);
lean_ctor_set(v_reuseFailAlloc_801_, 2, v_ngen_780_);
lean_ctor_set(v_reuseFailAlloc_801_, 3, v_auxDeclNGen_781_);
lean_ctor_set(v_reuseFailAlloc_801_, 4, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_801_, 5, v_cache_782_);
lean_ctor_set(v_reuseFailAlloc_801_, 6, v_messages_783_);
lean_ctor_set(v_reuseFailAlloc_801_, 7, v_infoState_784_);
lean_ctor_set(v_reuseFailAlloc_801_, 8, v_snapshotTasks_785_);
lean_ctor_set(v_reuseFailAlloc_801_, 9, v_newDecls_786_);
v___x_798_ = v_reuseFailAlloc_801_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_st_ref_set(v___y_771_, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v_traces_775_);
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
lean_dec_ref(v___x_826_);
if (lean_obj_tag(v_val_828_) == 1)
{
uint8_t v_v_829_; 
v_v_829_ = lean_ctor_get_uint8(v_val_828_, 0);
lean_dec_ref(v_val_828_);
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
lean_object* v_ref_884_; lean_object* v___x_885_; lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_931_; 
v_ref_884_ = lean_ctor_get(v___y_881_, 5);
v___x_885_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_931_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_931_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_931_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v_traceState_891_; lean_object* v_env_892_; lean_object* v_nextMacroScope_893_; lean_object* v_ngen_894_; lean_object* v_auxDeclNGen_895_; lean_object* v_cache_896_; lean_object* v_messages_897_; lean_object* v_infoState_898_; lean_object* v_snapshotTasks_899_; lean_object* v_newDecls_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_930_; 
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
v_newDecls_900_ = lean_ctor_get(v___x_890_, 9);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_930_ == 0)
{
v___x_902_ = v___x_890_;
v_isShared_903_ = v_isSharedCheck_930_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_newDecls_900_);
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
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_930_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint64_t v_tid_904_; lean_object* v_traces_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_929_; 
v_tid_904_ = lean_ctor_get_uint64(v_traceState_891_, sizeof(void*)*1);
v_traces_905_ = lean_ctor_get(v_traceState_891_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v_traceState_891_);
if (v_isSharedCheck_929_ == 0)
{
v___x_907_ = v_traceState_891_;
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_traces_905_);
lean_dec(v_traceState_891_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_929_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; double v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_909_ = lean_box(0);
v___x_910_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
v___x_911_ = 0;
v___x_912_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_913_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_913_, 0, v_cls_877_);
lean_ctor_set(v___x_913_, 1, v___x_909_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
lean_ctor_set_float(v___x_913_, sizeof(void*)*3, v___x_910_);
lean_ctor_set_float(v___x_913_, sizeof(void*)*3 + 8, v___x_910_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*3 + 16, v___x_911_);
v___x_914_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__2));
v___x_915_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v_a_886_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
lean_inc(v_ref_884_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v_ref_884_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_PersistentArray_push___redArg(v_traces_905_, v___x_916_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_917_);
v___x_919_ = v___x_907_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_917_);
lean_ctor_set_uint64(v_reuseFailAlloc_928_, sizeof(void*)*1, v_tid_904_);
v___x_919_ = v_reuseFailAlloc_928_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___x_919_);
v___x_921_ = v___x_902_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_env_892_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_nextMacroScope_893_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_ngen_894_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_auxDeclNGen_895_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_927_, 5, v_cache_896_);
lean_ctor_set(v_reuseFailAlloc_927_, 6, v_messages_897_);
lean_ctor_set(v_reuseFailAlloc_927_, 7, v_infoState_898_);
lean_ctor_set(v_reuseFailAlloc_927_, 8, v_snapshotTasks_899_);
lean_ctor_set(v_reuseFailAlloc_927_, 9, v_newDecls_900_);
v___x_921_ = v_reuseFailAlloc_927_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_922_ = lean_st_ref_set(v___y_882_, v___x_921_);
v___x_923_ = lean_box(0);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_923_);
v___x_925_ = v___x_888_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___boxed(lean_object* v_cls_932_, lean_object* v_msg_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_932_, v_msg_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(lean_object* v_opts_940_, lean_object* v_opt_941_){
_start:
{
lean_object* v_name_942_; lean_object* v_defValue_943_; lean_object* v_map_944_; lean_object* v___x_945_; 
v_name_942_ = lean_ctor_get(v_opt_941_, 0);
v_defValue_943_ = lean_ctor_get(v_opt_941_, 1);
v_map_944_ = lean_ctor_get(v_opts_940_, 0);
v___x_945_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_944_, v_name_942_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_inc(v_defValue_943_);
return v_defValue_943_;
}
else
{
lean_object* v_val_946_; 
v_val_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_val_946_);
lean_dec_ref(v___x_945_);
if (lean_obj_tag(v_val_946_) == 3)
{
lean_object* v_v_947_; 
v_v_947_ = lean_ctor_get(v_val_946_, 0);
lean_inc(v_v_947_);
lean_dec_ref(v_val_946_);
return v_v_947_;
}
else
{
lean_dec(v_val_946_);
lean_inc(v_defValue_943_);
return v_defValue_943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8___boxed(lean_object* v_opts_948_, lean_object* v_opt_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_948_, v_opt_949_);
lean_dec_ref(v_opt_949_);
lean_dec_ref(v_opts_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7(size_t v_sz_951_, size_t v_i_952_, lean_object* v_bs_953_){
_start:
{
uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_lt(v_i_952_, v_sz_951_);
if (v___x_954_ == 0)
{
return v_bs_953_;
}
else
{
lean_object* v_v_955_; lean_object* v_msg_956_; lean_object* v___x_957_; lean_object* v_bs_x27_958_; size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v_v_955_ = lean_array_uget_borrowed(v_bs_953_, v_i_952_);
v_msg_956_ = lean_ctor_get(v_v_955_, 1);
lean_inc_ref(v_msg_956_);
v___x_957_ = lean_unsigned_to_nat(0u);
v_bs_x27_958_ = lean_array_uset(v_bs_953_, v_i_952_, v___x_957_);
v___x_959_ = ((size_t)1ULL);
v___x_960_ = lean_usize_add(v_i_952_, v___x_959_);
v___x_961_ = lean_array_uset(v_bs_x27_958_, v_i_952_, v_msg_956_);
v_i_952_ = v___x_960_;
v_bs_953_ = v___x_961_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_963_, lean_object* v_i_964_, lean_object* v_bs_965_){
_start:
{
size_t v_sz_boxed_966_; size_t v_i_boxed_967_; lean_object* v_res_968_; 
v_sz_boxed_966_ = lean_unbox_usize(v_sz_963_);
lean_dec(v_sz_963_);
v_i_boxed_967_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7(v_sz_boxed_966_, v_i_boxed_967_, v_bs_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(lean_object* v_oldTraces_969_, lean_object* v_data_970_, lean_object* v_ref_971_, lean_object* v_msg_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_fileName_978_; lean_object* v_fileMap_979_; lean_object* v_options_980_; lean_object* v_currRecDepth_981_; lean_object* v_maxRecDepth_982_; lean_object* v_ref_983_; lean_object* v_currNamespace_984_; lean_object* v_openDecls_985_; lean_object* v_initHeartbeats_986_; lean_object* v_maxHeartbeats_987_; lean_object* v_quotContext_988_; lean_object* v_currMacroScope_989_; uint8_t v_diag_990_; lean_object* v_cancelTk_x3f_991_; uint8_t v_suppressElabErrors_992_; lean_object* v_inheritedTraceOptions_993_; lean_object* v___x_994_; lean_object* v_traceState_995_; lean_object* v_traces_996_; lean_object* v_ref_997_; lean_object* v___x_998_; lean_object* v___x_999_; size_t v_sz_1000_; size_t v___x_1001_; lean_object* v___x_1002_; lean_object* v_msg_1003_; lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1043_; 
v_fileName_978_ = lean_ctor_get(v___y_975_, 0);
v_fileMap_979_ = lean_ctor_get(v___y_975_, 1);
v_options_980_ = lean_ctor_get(v___y_975_, 2);
v_currRecDepth_981_ = lean_ctor_get(v___y_975_, 3);
v_maxRecDepth_982_ = lean_ctor_get(v___y_975_, 4);
v_ref_983_ = lean_ctor_get(v___y_975_, 5);
v_currNamespace_984_ = lean_ctor_get(v___y_975_, 6);
v_openDecls_985_ = lean_ctor_get(v___y_975_, 7);
v_initHeartbeats_986_ = lean_ctor_get(v___y_975_, 8);
v_maxHeartbeats_987_ = lean_ctor_get(v___y_975_, 9);
v_quotContext_988_ = lean_ctor_get(v___y_975_, 10);
v_currMacroScope_989_ = lean_ctor_get(v___y_975_, 11);
v_diag_990_ = lean_ctor_get_uint8(v___y_975_, sizeof(void*)*14);
v_cancelTk_x3f_991_ = lean_ctor_get(v___y_975_, 12);
v_suppressElabErrors_992_ = lean_ctor_get_uint8(v___y_975_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_993_ = lean_ctor_get(v___y_975_, 13);
v___x_994_ = lean_st_ref_get(v___y_976_);
v_traceState_995_ = lean_ctor_get(v___x_994_, 4);
lean_inc_ref(v_traceState_995_);
lean_dec(v___x_994_);
v_traces_996_ = lean_ctor_get(v_traceState_995_, 0);
lean_inc_ref(v_traces_996_);
lean_dec_ref(v_traceState_995_);
v_ref_997_ = l_Lean_replaceRef(v_ref_971_, v_ref_983_);
lean_inc_ref(v_inheritedTraceOptions_993_);
lean_inc(v_cancelTk_x3f_991_);
lean_inc(v_currMacroScope_989_);
lean_inc(v_quotContext_988_);
lean_inc(v_maxHeartbeats_987_);
lean_inc(v_initHeartbeats_986_);
lean_inc(v_openDecls_985_);
lean_inc(v_currNamespace_984_);
lean_inc(v_maxRecDepth_982_);
lean_inc(v_currRecDepth_981_);
lean_inc_ref(v_options_980_);
lean_inc_ref(v_fileMap_979_);
lean_inc_ref(v_fileName_978_);
v___x_998_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_998_, 0, v_fileName_978_);
lean_ctor_set(v___x_998_, 1, v_fileMap_979_);
lean_ctor_set(v___x_998_, 2, v_options_980_);
lean_ctor_set(v___x_998_, 3, v_currRecDepth_981_);
lean_ctor_set(v___x_998_, 4, v_maxRecDepth_982_);
lean_ctor_set(v___x_998_, 5, v_ref_997_);
lean_ctor_set(v___x_998_, 6, v_currNamespace_984_);
lean_ctor_set(v___x_998_, 7, v_openDecls_985_);
lean_ctor_set(v___x_998_, 8, v_initHeartbeats_986_);
lean_ctor_set(v___x_998_, 9, v_maxHeartbeats_987_);
lean_ctor_set(v___x_998_, 10, v_quotContext_988_);
lean_ctor_set(v___x_998_, 11, v_currMacroScope_989_);
lean_ctor_set(v___x_998_, 12, v_cancelTk_x3f_991_);
lean_ctor_set(v___x_998_, 13, v_inheritedTraceOptions_993_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*14, v_diag_990_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*14 + 1, v_suppressElabErrors_992_);
v___x_999_ = l_Lean_PersistentArray_toArray___redArg(v_traces_996_);
lean_dec_ref(v_traces_996_);
v_sz_1000_ = lean_array_size(v___x_999_);
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6_spec__7(v_sz_1000_, v___x_1001_, v___x_999_);
v_msg_1003_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1003_, 0, v_data_970_);
lean_ctor_set(v_msg_1003_, 1, v_msg_972_);
lean_ctor_set(v_msg_1003_, 2, v___x_1002_);
v___x_1004_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0_spec__0(v_msg_1003_, v___y_973_, v___y_974_, v___x_998_, v___y_976_);
lean_dec_ref(v___x_998_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1043_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1043_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v_traceState_1010_; lean_object* v_env_1011_; lean_object* v_nextMacroScope_1012_; lean_object* v_ngen_1013_; lean_object* v_auxDeclNGen_1014_; lean_object* v_cache_1015_; lean_object* v_messages_1016_; lean_object* v_infoState_1017_; lean_object* v_snapshotTasks_1018_; lean_object* v_newDecls_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1042_; 
v___x_1009_ = lean_st_ref_take(v___y_976_);
v_traceState_1010_ = lean_ctor_get(v___x_1009_, 4);
v_env_1011_ = lean_ctor_get(v___x_1009_, 0);
v_nextMacroScope_1012_ = lean_ctor_get(v___x_1009_, 1);
v_ngen_1013_ = lean_ctor_get(v___x_1009_, 2);
v_auxDeclNGen_1014_ = lean_ctor_get(v___x_1009_, 3);
v_cache_1015_ = lean_ctor_get(v___x_1009_, 5);
v_messages_1016_ = lean_ctor_get(v___x_1009_, 6);
v_infoState_1017_ = lean_ctor_get(v___x_1009_, 7);
v_snapshotTasks_1018_ = lean_ctor_get(v___x_1009_, 8);
v_newDecls_1019_ = lean_ctor_get(v___x_1009_, 9);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1021_ = v___x_1009_;
v_isShared_1022_ = v_isSharedCheck_1042_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_newDecls_1019_);
lean_inc(v_snapshotTasks_1018_);
lean_inc(v_infoState_1017_);
lean_inc(v_messages_1016_);
lean_inc(v_cache_1015_);
lean_inc(v_traceState_1010_);
lean_inc(v_auxDeclNGen_1014_);
lean_inc(v_ngen_1013_);
lean_inc(v_nextMacroScope_1012_);
lean_inc(v_env_1011_);
lean_dec(v___x_1009_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1042_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
uint64_t v_tid_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1040_; 
v_tid_1023_ = lean_ctor_get_uint64(v_traceState_1010_, sizeof(void*)*1);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_traceState_1010_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_traceState_1010_, 0);
lean_dec(v_unused_1041_);
v___x_1025_ = v_traceState_1010_;
v_isShared_1026_ = v_isSharedCheck_1040_;
goto v_resetjp_1024_;
}
else
{
lean_dec(v_traceState_1010_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1040_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_ref_971_);
lean_ctor_set(v___x_1027_, 1, v_a_1005_);
v___x_1028_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_969_, v___x_1027_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1028_);
v___x_1030_ = v___x_1025_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1028_);
lean_ctor_set_uint64(v_reuseFailAlloc_1039_, sizeof(void*)*1, v_tid_1023_);
v___x_1030_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 4, v___x_1030_);
v___x_1032_ = v___x_1021_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_env_1011_);
lean_ctor_set(v_reuseFailAlloc_1038_, 1, v_nextMacroScope_1012_);
lean_ctor_set(v_reuseFailAlloc_1038_, 2, v_ngen_1013_);
lean_ctor_set(v_reuseFailAlloc_1038_, 3, v_auxDeclNGen_1014_);
lean_ctor_set(v_reuseFailAlloc_1038_, 4, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1038_, 5, v_cache_1015_);
lean_ctor_set(v_reuseFailAlloc_1038_, 6, v_messages_1016_);
lean_ctor_set(v_reuseFailAlloc_1038_, 7, v_infoState_1017_);
lean_ctor_set(v_reuseFailAlloc_1038_, 8, v_snapshotTasks_1018_);
lean_ctor_set(v_reuseFailAlloc_1038_, 9, v_newDecls_1019_);
v___x_1032_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1033_ = lean_st_ref_set(v___y_976_, v___x_1032_);
v___x_1034_ = lean_box(0);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1034_);
v___x_1036_ = v___x_1007_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6___boxed(lean_object* v_oldTraces_1044_, lean_object* v_data_1045_, lean_object* v_ref_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_oldTraces_1044_, v_data_1045_, v_ref_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v_x_1054_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v_x_1054_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v_x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
v_a_1064_ = lean_ctor_get(v_x_1054_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v_x_1054_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v_x_1054_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 0);
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg___boxed(lean_object* v_x_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_x_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(lean_object* v_e_1075_){
_start:
{
if (lean_obj_tag(v_e_1075_) == 0)
{
uint8_t v___x_1076_; 
v___x_1076_ = 2;
return v___x_1076_;
}
else
{
uint8_t v___x_1077_; 
v___x_1077_ = 0;
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5___boxed(lean_object* v_e_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_e_1078_);
lean_dec_ref(v_e_1078_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__0));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__2));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4(void){
_start:
{
lean_object* v___x_1087_; double v___x_1088_; 
v___x_1087_ = lean_unsigned_to_nat(1000u);
v___x_1088_ = lean_float_of_nat(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(lean_object* v_cls_1089_, uint8_t v_collapsed_1090_, lean_object* v_tag_1091_, lean_object* v_opts_1092_, uint8_t v_clsEnabled_1093_, lean_object* v_oldTraces_1094_, lean_object* v_msg_1095_, lean_object* v_resStartStop_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1194_; 
v_fst_1102_ = lean_ctor_get(v_resStartStop_1096_, 0);
v_snd_1103_ = lean_ctor_get(v_resStartStop_1096_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_resStartStop_1096_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1105_ = v_resStartStop_1096_;
v_isShared_1106_ = v_isSharedCheck_1194_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_snd_1103_);
lean_inc(v_fst_1102_);
lean_dec(v_resStartStop_1096_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1194_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v_data_1110_; lean_object* v_fst_1113_; lean_object* v_snd_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1193_; 
v_fst_1113_ = lean_ctor_get(v_snd_1103_, 0);
v_snd_1114_ = lean_ctor_get(v_snd_1103_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_snd_1103_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1116_ = v_snd_1103_;
v_isShared_1117_ = v_isSharedCheck_1193_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_snd_1114_);
lean_inc(v_fst_1113_);
lean_dec(v_snd_1103_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1193_;
goto v_resetjp_1115_;
}
v___jp_1107_:
{
lean_object* v___x_1111_; 
lean_inc(v___y_1109_);
v___x_1111_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_oldTraces_1094_, v_data_1110_, v___y_1109_, v___y_1108_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref(v___x_1111_);
v___x_1112_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_1102_);
return v___x_1112_;
}
else
{
lean_dec(v_fst_1102_);
return v___x_1111_;
}
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; lean_object* v___y_1121_; lean_object* v_a_1122_; uint8_t v___y_1146_; double v___y_1178_; 
v___x_1118_ = l_Lean_trace_profiler;
v___x_1119_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1092_, v___x_1118_);
if (v___x_1119_ == 0)
{
v___y_1146_ = v___x_1119_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1184_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_1092_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; lean_object* v___x_1186_; double v___x_1187_; double v___x_1188_; double v___x_1189_; 
v___x_1185_ = l_Lean_trace_profiler_threshold;
v___x_1186_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1092_, v___x_1185_);
v___x_1187_ = lean_float_of_nat(v___x_1186_);
v___x_1188_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4);
v___x_1189_ = lean_float_div(v___x_1187_, v___x_1188_);
v___y_1178_ = v___x_1189_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; double v___x_1192_; 
v___x_1190_ = l_Lean_trace_profiler_threshold;
v___x_1191_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_1092_, v___x_1190_);
v___x_1192_ = lean_float_of_nat(v___x_1191_);
v___y_1178_ = v___x_1192_;
goto v___jp_1177_;
}
}
v___jp_1120_:
{
uint8_t v_result_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v_result_1123_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__5(v_fst_1102_);
v___x_1124_ = l_Lean_TraceResult_toEmoji(v_result_1123_);
v___x_1125_ = l_Lean_stringToMessageData(v___x_1124_);
v___x_1126_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 7);
lean_ctor_set(v___x_1116_, 1, v___x_1126_);
lean_ctor_set(v___x_1116_, 0, v___x_1125_);
v___x_1128_ = v___x_1116_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v_m_1130_; 
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 7);
lean_ctor_set(v___x_1105_, 1, v_a_1122_);
lean_ctor_set(v___x_1105_, 0, v___x_1128_);
v_m_1130_ = v___x_1105_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_a_1122_);
v_m_1130_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; double v___x_1133_; lean_object* v_data_1134_; 
v___x_1131_ = lean_box(v_result_1123_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
v___x_1133_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_1091_);
lean_inc_ref(v___x_1132_);
lean_inc(v_cls_1089_);
v_data_1134_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1134_, 0, v_cls_1089_);
lean_ctor_set(v_data_1134_, 1, v___x_1132_);
lean_ctor_set(v_data_1134_, 2, v_tag_1091_);
lean_ctor_set_float(v_data_1134_, sizeof(void*)*3, v___x_1133_);
lean_ctor_set_float(v_data_1134_, sizeof(void*)*3 + 8, v___x_1133_);
lean_ctor_set_uint8(v_data_1134_, sizeof(void*)*3 + 16, v_collapsed_1090_);
if (v___x_1119_ == 0)
{
lean_dec_ref(v___x_1132_);
lean_dec(v_snd_1114_);
lean_dec(v_fst_1113_);
lean_dec_ref(v_tag_1091_);
lean_dec(v_cls_1089_);
v___y_1108_ = v_m_1130_;
v___y_1109_ = v___y_1121_;
v_data_1110_ = v_data_1134_;
goto v___jp_1107_;
}
else
{
lean_object* v_data_1135_; double v___x_1136_; double v___x_1137_; 
lean_dec_ref(v_data_1134_);
v_data_1135_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1135_, 0, v_cls_1089_);
lean_ctor_set(v_data_1135_, 1, v___x_1132_);
lean_ctor_set(v_data_1135_, 2, v_tag_1091_);
v___x_1136_ = lean_unbox_float(v_fst_1113_);
lean_dec(v_fst_1113_);
lean_ctor_set_float(v_data_1135_, sizeof(void*)*3, v___x_1136_);
v___x_1137_ = lean_unbox_float(v_snd_1114_);
lean_dec(v_snd_1114_);
lean_ctor_set_float(v_data_1135_, sizeof(void*)*3 + 8, v___x_1137_);
lean_ctor_set_uint8(v_data_1135_, sizeof(void*)*3 + 16, v_collapsed_1090_);
v___y_1108_ = v_m_1130_;
v___y_1109_ = v___y_1121_;
v_data_1110_ = v_data_1135_;
goto v___jp_1107_;
}
}
}
}
v___jp_1140_:
{
lean_object* v_ref_1141_; lean_object* v___x_1142_; 
v_ref_1141_ = lean_ctor_get(v___y_1099_, 5);
lean_inc(v___y_1100_);
lean_inc_ref(v___y_1099_);
lean_inc(v___y_1098_);
lean_inc_ref(v___y_1097_);
lean_inc(v_fst_1102_);
v___x_1142_ = lean_apply_6(v_msg_1095_, v_fst_1102_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, lean_box(0));
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
lean_inc(v_a_1143_);
lean_dec_ref(v___x_1142_);
v___y_1121_ = v_ref_1141_;
v_a_1122_ = v_a_1143_;
goto v___jp_1120_;
}
else
{
lean_object* v___x_1144_; 
lean_dec_ref(v___x_1142_);
v___x_1144_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3);
v___y_1121_ = v_ref_1141_;
v_a_1122_ = v___x_1144_;
goto v___jp_1120_;
}
}
v___jp_1145_:
{
if (v_clsEnabled_1093_ == 0)
{
if (v___y_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v_traceState_1148_; lean_object* v_env_1149_; lean_object* v_nextMacroScope_1150_; lean_object* v_ngen_1151_; lean_object* v_auxDeclNGen_1152_; lean_object* v_cache_1153_; lean_object* v_messages_1154_; lean_object* v_infoState_1155_; lean_object* v_snapshotTasks_1156_; lean_object* v_newDecls_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1176_; 
lean_del_object(v___x_1116_);
lean_dec(v_snd_1114_);
lean_dec(v_fst_1113_);
lean_del_object(v___x_1105_);
lean_dec_ref(v_msg_1095_);
lean_dec_ref(v_tag_1091_);
lean_dec(v_cls_1089_);
v___x_1147_ = lean_st_ref_take(v___y_1100_);
v_traceState_1148_ = lean_ctor_get(v___x_1147_, 4);
v_env_1149_ = lean_ctor_get(v___x_1147_, 0);
v_nextMacroScope_1150_ = lean_ctor_get(v___x_1147_, 1);
v_ngen_1151_ = lean_ctor_get(v___x_1147_, 2);
v_auxDeclNGen_1152_ = lean_ctor_get(v___x_1147_, 3);
v_cache_1153_ = lean_ctor_get(v___x_1147_, 5);
v_messages_1154_ = lean_ctor_get(v___x_1147_, 6);
v_infoState_1155_ = lean_ctor_get(v___x_1147_, 7);
v_snapshotTasks_1156_ = lean_ctor_get(v___x_1147_, 8);
v_newDecls_1157_ = lean_ctor_get(v___x_1147_, 9);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1159_ = v___x_1147_;
v_isShared_1160_ = v_isSharedCheck_1176_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_newDecls_1157_);
lean_inc(v_snapshotTasks_1156_);
lean_inc(v_infoState_1155_);
lean_inc(v_messages_1154_);
lean_inc(v_cache_1153_);
lean_inc(v_traceState_1148_);
lean_inc(v_auxDeclNGen_1152_);
lean_inc(v_ngen_1151_);
lean_inc(v_nextMacroScope_1150_);
lean_inc(v_env_1149_);
lean_dec(v___x_1147_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1176_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint64_t v_tid_1161_; lean_object* v_traces_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1175_; 
v_tid_1161_ = lean_ctor_get_uint64(v_traceState_1148_, sizeof(void*)*1);
v_traces_1162_ = lean_ctor_get(v_traceState_1148_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_traceState_1148_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1164_ = v_traceState_1148_;
v_isShared_1165_ = v_isSharedCheck_1175_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_traces_1162_);
lean_dec(v_traceState_1148_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1175_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1094_, v_traces_1162_);
lean_dec_ref(v_traces_1162_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1166_);
lean_ctor_set_uint64(v_reuseFailAlloc_1174_, sizeof(void*)*1, v_tid_1161_);
v___x_1168_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 4, v___x_1168_);
v___x_1170_ = v___x_1159_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_env_1149_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_nextMacroScope_1150_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v_ngen_1151_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_auxDeclNGen_1152_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1173_, 5, v_cache_1153_);
lean_ctor_set(v_reuseFailAlloc_1173_, 6, v_messages_1154_);
lean_ctor_set(v_reuseFailAlloc_1173_, 7, v_infoState_1155_);
lean_ctor_set(v_reuseFailAlloc_1173_, 8, v_snapshotTasks_1156_);
lean_ctor_set(v_reuseFailAlloc_1173_, 9, v_newDecls_1157_);
v___x_1170_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_st_ref_set(v___y_1100_, v___x_1170_);
v___x_1172_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_1102_);
return v___x_1172_;
}
}
}
}
}
else
{
goto v___jp_1140_;
}
}
else
{
goto v___jp_1140_;
}
}
v___jp_1177_:
{
double v___x_1179_; double v___x_1180_; double v___x_1181_; uint8_t v___x_1182_; 
v___x_1179_ = lean_unbox_float(v_snd_1114_);
v___x_1180_ = lean_unbox_float(v_fst_1113_);
v___x_1181_ = lean_float_sub(v___x_1179_, v___x_1180_);
v___x_1182_ = lean_float_decLt(v___y_1178_, v___x_1181_);
v___y_1146_ = v___x_1182_;
goto v___jp_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___boxed(lean_object* v_cls_1195_, lean_object* v_collapsed_1196_, lean_object* v_tag_1197_, lean_object* v_opts_1198_, lean_object* v_clsEnabled_1199_, lean_object* v_oldTraces_1200_, lean_object* v_msg_1201_, lean_object* v_resStartStop_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v_collapsed_boxed_1208_; uint8_t v_clsEnabled_boxed_1209_; lean_object* v_res_1210_; 
v_collapsed_boxed_1208_ = lean_unbox(v_collapsed_1196_);
v_clsEnabled_boxed_1209_ = lean_unbox(v_clsEnabled_1199_);
v_res_1210_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1195_, v_collapsed_boxed_1208_, v_tag_1197_, v_opts_1198_, v_clsEnabled_boxed_1209_, v_oldTraces_1200_, v_msg_1201_, v_resStartStop_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec_ref(v_opts_1198_);
return v_res_1210_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3(void){
_start:
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1213_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__3);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_box(0);
v___x_1217_ = lean_unsigned_to_nat(16u);
v___x_1218_ = lean_mk_array(v___x_1217_, v___x_1216_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__1);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5(void){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1223_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1224_ = 1;
v___x_1225_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1222_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*2, v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1226_ = lean_unsigned_to_nat(32u);
v___x_1227_ = lean_mk_empty_array_with_capacity(v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8(void){
_start:
{
size_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1229_ = ((size_t)5ULL);
v___x_1230_ = lean_unsigned_to_nat(0u);
v___x_1231_ = lean_unsigned_to_nat(32u);
v___x_1232_ = lean_mk_empty_array_with_capacity(v___x_1231_);
v___x_1233_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__7);
v___x_1234_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v___x_1232_);
lean_ctor_set(v___x_1234_, 2, v___x_1230_);
lean_ctor_set(v___x_1234_, 3, v___x_1230_);
lean_ctor_set_usize(v___x_1234_, 4, v___x_1229_);
return v___x_1234_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__8);
v___x_1236_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1237_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
lean_ctor_set(v___x_1237_, 2, v___x_1236_);
lean_ctor_set(v___x_1237_, 3, v___x_1235_);
return v___x_1237_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___x_1238_);
return v___x_1240_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__9);
v___x_1242_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__6);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
lean_ctor_set(v___x_1243_, 1, v___x_1241_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* v_declName_1244_, lean_object* v_as_1245_, size_t v_i_1246_, size_t v_stop_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_usize_dec_eq(v_i_1246_, v_stop_1247_);
if (v___x_1254_ == 0)
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_array_uget_borrowed(v_as_1245_, v_i_1246_);
lean_inc(v___x_1255_);
lean_inc(v_declName_1244_);
v___x_1256_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1244_, v___x_1255_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; size_t v___x_1258_; size_t v___x_1259_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1257_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_add(v_i_1246_, v___x_1258_);
v_i_1246_ = v___x_1259_;
v_b_1248_ = v_a_1257_;
goto _start;
}
else
{
lean_dec(v_declName_1244_);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_declName_1244_);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_b_1248_);
return v___x_1261_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__11));
v___x_1264_ = l_Lean_stringToMessageData(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20(void){
_start:
{
lean_object* v_cls_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_cls_1277_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_1279_ = l_Lean_Name_append(v___x_1278_, v_cls_1277_);
return v___x_1279_;
}
}
static double _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21(void){
_start:
{
lean_object* v___x_1280_; double v___x_1281_; 
v___x_1280_ = lean_unsigned_to_nat(1000000000u);
v___x_1281_ = lean_float_of_nat(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__22));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__24));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__26));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__28));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__30));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(lean_object* v_val_1297_, lean_object* v___x_1298_, lean_object* v_declName_1299_, lean_object* v_____r_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_array_get_size(v_val_1297_);
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_nat_dec_lt(v___x_1298_, v___x_1306_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec(v_declName_1299_);
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1307_);
return v___x_1309_;
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_le(v___x_1306_, v___x_1306_);
if (v___x_1310_ == 0)
{
if (v___x_1308_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_declName_1299_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1307_);
return v___x_1311_;
}
else
{
size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = ((size_t)0ULL);
v___x_1313_ = lean_usize_of_nat(v___x_1306_);
v___x_1314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1299_, v_val_1297_, v___x_1312_, v___x_1313_, v___x_1307_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1314_;
}
}
else
{
size_t v___x_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = ((size_t)0ULL);
v___x_1316_ = lean_usize_of_nat(v___x_1306_);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1299_, v_val_1297_, v___x_1315_, v___x_1316_, v___x_1307_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1317_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__32));
v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
return v___x_1320_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__34));
v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
return v___x_1323_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__36));
v___x_1326_ = l_Lean_stringToMessageData(v___x_1325_);
return v___x_1326_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__38));
v___x_1329_ = l_Lean_stringToMessageData(v___x_1328_);
return v___x_1329_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1331_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__40));
v___x_1332_ = l_Lean_stringToMessageData(v___x_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* v_declName_1333_, lean_object* v_mvarId_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_options_1346_; uint8_t v_hasTrace_1347_; 
v_options_1346_ = lean_ctor_get(v_a_1337_, 2);
v_hasTrace_1347_ = lean_ctor_get_uint8(v_options_1346_, sizeof(void*)*1);
if (v_hasTrace_1347_ == 0)
{
lean_object* v___x_1348_; 
lean_inc(v_mvarId_1334_);
v___x_1348_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1520_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1520_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1520_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_unbox(v_a_1349_);
lean_dec(v_a_1349_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_del_object(v___x_1351_);
lean_inc(v_mvarId_1334_);
v___x_1354_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1507_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1507_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1507_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_unbox(v_a_1355_);
lean_dec(v_a_1355_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; 
lean_del_object(v___x_1357_);
lean_inc(v_mvarId_1334_);
v___x_1360_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
if (lean_obj_tag(v_a_1361_) == 1)
{
lean_object* v_val_1362_; 
lean_dec(v_mvarId_1334_);
v_val_1362_ = lean_ctor_get(v_a_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref(v_a_1361_);
v_mvarId_1334_ = v_val_1362_;
goto _start;
}
else
{
lean_object* v___x_1364_; 
lean_dec(v_a_1361_);
lean_inc(v_mvarId_1334_);
v___x_1364_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
if (lean_obj_tag(v_a_1365_) == 1)
{
lean_object* v_val_1366_; 
lean_dec(v_mvarId_1334_);
v_val_1366_ = lean_ctor_get(v_a_1365_, 0);
lean_inc(v_val_1366_);
lean_dec_ref(v_a_1365_);
v_mvarId_1334_ = v_val_1366_;
goto _start;
}
else
{
uint8_t v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v_a_1365_);
v___x_1368_ = 1;
lean_inc(v_mvarId_1334_);
v___x_1369_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1334_, v___x_1368_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
if (lean_obj_tag(v_a_1370_) == 1)
{
lean_object* v_val_1371_; 
lean_dec(v_mvarId_1334_);
v_val_1371_ = lean_ctor_get(v_a_1370_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v_a_1370_);
v_mvarId_1334_ = v_val_1371_;
goto _start;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
lean_dec(v_a_1370_);
v___x_1373_ = lean_unsigned_to_nat(100000u);
v___x_1374_ = lean_unsigned_to_nat(2u);
v___x_1375_ = 0;
v___x_1376_ = lean_box(0);
v___x_1377_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1377_, 0, v___x_1373_);
lean_ctor_set(v___x_1377_, 1, v___x_1374_);
lean_ctor_set(v___x_1377_, 2, v___x_1376_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 1, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 2, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 3, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 4, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 5, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 6, v___x_1375_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 7, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 8, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 9, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 10, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 11, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 12, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 13, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 14, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 15, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 16, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 17, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 18, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 19, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 20, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 21, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 22, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 23, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 24, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 25, v___x_1368_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 26, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 27, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1377_, sizeof(void*)*3 + 28, v_hasTrace_1347_);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1380_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__5);
v___x_1381_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1377_, v___x_1379_, v___x_1380_, v_a_1335_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1334_);
v___x_1384_ = l_Lean_Meta_simpTargetStar(v_mvarId_1334_, v_a_1382_, v___x_1379_, v___x_1376_, v___x_1383_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1462_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1462_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1462_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v_fst_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1460_; 
v_fst_1389_ = lean_ctor_get(v_a_1385_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_a_1385_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_a_1385_, 1);
lean_dec(v_unused_1461_);
v___x_1391_ = v_a_1385_;
v_isShared_1392_ = v_isSharedCheck_1460_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_fst_1389_);
lean_dec(v_a_1385_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1460_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
switch(lean_obj_tag(v_fst_1389_))
{
case 0:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_del_object(v___x_1391_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v___x_1393_ = lean_box(0);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1393_);
v___x_1395_ = v___x_1387_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
case 1:
{
lean_object* v___x_1397_; 
lean_del_object(v___x_1387_);
lean_inc(v_declName_1333_);
lean_inc(v_mvarId_1334_);
v___x_1397_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1334_, v_declName_1333_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref(v___x_1397_);
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1399_; 
lean_del_object(v___x_1391_);
lean_dec(v_mvarId_1334_);
v_val_1399_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_val_1399_);
lean_dec_ref(v_a_1398_);
v_mvarId_1334_ = v_val_1399_;
goto _start;
}
else
{
lean_object* v___x_1401_; 
lean_dec(v_a_1398_);
lean_inc(v_mvarId_1334_);
v___x_1401_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1441_; 
v_a_1402_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1404_ = v___x_1401_;
v_isShared_1405_ = v_isSharedCheck_1441_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1401_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1441_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
if (lean_obj_tag(v_a_1402_) == 1)
{
lean_object* v_val_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
lean_del_object(v___x_1391_);
lean_dec(v_mvarId_1334_);
v_val_1406_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_val_1406_);
lean_dec_ref(v_a_1402_);
v___x_1407_ = lean_array_get_size(v_val_1406_);
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_nat_dec_lt(v___x_1378_, v___x_1407_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1411_; 
lean_dec(v_val_1406_);
lean_dec(v_declName_1333_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1408_);
v___x_1411_ = v___x_1404_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1408_);
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
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_le(v___x_1407_, v___x_1407_);
if (v___x_1413_ == 0)
{
if (v___x_1409_ == 0)
{
lean_object* v___x_1415_; 
lean_dec(v_val_1406_);
lean_dec(v_declName_1333_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v___x_1408_);
v___x_1415_ = v___x_1404_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1408_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
lean_del_object(v___x_1404_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1407_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1333_, v_val_1406_, v___x_1417_, v___x_1418_, v___x_1408_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_val_1406_);
return v___x_1419_;
}
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1404_);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1407_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1333_, v_val_1406_, v___x_1420_, v___x_1421_, v___x_1408_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_val_1406_);
return v___x_1422_;
}
}
}
else
{
lean_object* v___x_1423_; 
lean_del_object(v___x_1404_);
lean_dec(v_a_1402_);
lean_inc(v_mvarId_1334_);
v___x_1423_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1334_, v___x_1368_, v___x_1368_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1423_);
if (lean_obj_tag(v_a_1424_) == 1)
{
lean_object* v_val_1425_; lean_object* v___x_1426_; 
lean_del_object(v___x_1391_);
lean_dec(v_mvarId_1334_);
v_val_1425_ = lean_ctor_get(v_a_1424_, 0);
lean_inc(v_val_1425_);
lean_dec_ref(v_a_1424_);
v___x_1426_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1333_, v_val_1425_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec(v_a_1424_);
lean_dec(v_declName_1333_);
v___x_1427_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_mvarId_1334_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 7);
lean_ctor_set(v___x_1391_, 1, v___x_1428_);
lean_ctor_set(v___x_1391_, 0, v___x_1427_);
v___x_1430_ = v___x_1391_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1430_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1431_;
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_del_object(v___x_1391_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1433_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1423_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1423_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_del_object(v___x_1391_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1442_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1401_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1401_);
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
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_del_object(v___x_1391_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1450_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1397_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1397_);
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
default: 
{
lean_object* v_mvarId_1458_; 
lean_del_object(v___x_1391_);
lean_del_object(v___x_1387_);
lean_dec(v_mvarId_1334_);
v_mvarId_1458_ = lean_ctor_get(v_fst_1389_, 0);
lean_inc(v_mvarId_1458_);
lean_dec_ref(v_fst_1389_);
v_mvarId_1334_ = v_mvarId_1458_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1463_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1384_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1384_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1471_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1381_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1381_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1479_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1369_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1369_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
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
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1487_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1364_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1364_);
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
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1495_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1360_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1360_);
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
lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v___x_1503_ = lean_box(0);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1503_);
v___x_1505_ = v___x_1357_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
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
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1508_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1510_ = v___x_1354_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1354_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_a_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v___x_1516_ = lean_box(0);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1516_);
v___x_1518_ = v___x_1351_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1521_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1348_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1348_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1529_; lean_object* v___f_1530_; lean_object* v_cls_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v_a_1538_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v_a_1550_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v_a_1555_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v_a_1566_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v_a_1581_; lean_object* v___y_1584_; lean_object* v___y_1585_; lean_object* v_a_1586_; lean_object* v___y_1589_; lean_object* v___y_1590_; lean_object* v___y_1591_; 
v_inheritedTraceOptions_1529_ = lean_ctor_get(v_a_1337_, 13);
lean_inc(v_mvarId_1334_);
v___f_1530_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1530_, 0, v_mvarId_1334_);
v_cls_1531_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_1532_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_1533_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_1534_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1529_, v_options_1346_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = l_Lean_trace_profiler;
v___x_1861_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1346_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v___f_1530_);
lean_inc(v_mvarId_1334_);
v___x_1862_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; uint8_t v___x_1864_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref(v___x_1862_);
v___x_1864_ = lean_unbox(v_a_1863_);
lean_dec(v_a_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_inc(v_mvarId_1334_);
v___x_1865_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; uint8_t v___x_1867_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc(v_a_1866_);
lean_dec_ref(v___x_1865_);
v___x_1867_ = lean_unbox(v_a_1866_);
lean_dec(v_a_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_inc(v_mvarId_1334_);
v___x_1868_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
if (lean_obj_tag(v_a_1869_) == 1)
{
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1870_; 
v_val_1870_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v_a_1869_);
v_mvarId_1334_ = v_val_1870_;
goto _start;
}
else
{
lean_object* v_val_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_val_1872_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_val_1872_);
lean_dec_ref(v_a_1869_);
v___x_1873_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1874_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1873_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_dec_ref(v___x_1874_);
v_mvarId_1334_ = v_val_1872_;
goto _start;
}
else
{
lean_dec(v_val_1872_);
lean_dec(v_declName_1333_);
return v___x_1874_;
}
}
}
else
{
lean_object* v___x_1876_; 
lean_dec(v_a_1869_);
lean_inc(v_mvarId_1334_);
v___x_1876_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
if (lean_obj_tag(v_a_1877_) == 1)
{
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1878_; 
v_val_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_val_1878_);
lean_dec_ref(v_a_1877_);
v_mvarId_1334_ = v_val_1878_;
goto _start;
}
else
{
lean_object* v_val_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_val_1880_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_val_1880_);
lean_dec_ref(v_a_1877_);
v___x_1881_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1882_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1881_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_dec_ref(v___x_1882_);
v_mvarId_1334_ = v_val_1880_;
goto _start;
}
else
{
lean_dec(v_val_1880_);
lean_dec(v_declName_1333_);
return v___x_1882_;
}
}
}
else
{
lean_object* v___x_1884_; 
lean_dec(v_a_1877_);
lean_inc(v_mvarId_1334_);
v___x_1884_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1334_, v_hasTrace_1347_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
if (lean_obj_tag(v_a_1885_) == 1)
{
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1886_; 
v_val_1886_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_val_1886_);
lean_dec_ref(v_a_1885_);
v_mvarId_1334_ = v_val_1886_;
goto _start;
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_val_1888_ = lean_ctor_get(v_a_1885_, 0);
lean_inc(v_val_1888_);
lean_dec_ref(v_a_1885_);
v___x_1889_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1890_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1889_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_dec_ref(v___x_1890_);
v_mvarId_1334_ = v_val_1888_;
goto _start;
}
else
{
lean_dec(v_val_1888_);
lean_dec(v_declName_1333_);
return v___x_1890_;
}
}
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v_a_1885_);
v___x_1892_ = lean_unsigned_to_nat(100000u);
v___x_1893_ = lean_unsigned_to_nat(2u);
v___x_1894_ = 0;
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1896_, 0, v___x_1892_);
lean_ctor_set(v___x_1896_, 1, v___x_1893_);
lean_ctor_set(v___x_1896_, 2, v___x_1895_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 1, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 2, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 3, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 4, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 5, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 6, v___x_1894_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 7, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 8, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 9, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 10, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 11, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 12, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 13, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 14, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 15, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 16, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 17, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 18, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 19, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 20, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 21, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 22, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 23, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 24, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 25, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 26, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 27, v___x_1861_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*3 + 28, v___x_1861_);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1899_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1900_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1901_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
lean_ctor_set_uint8(v___x_1901_, sizeof(void*)*2, v_hasTrace_1347_);
v___x_1902_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1896_, v___x_1898_, v___x_1901_, v_a_1335_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1334_);
v___x_1905_ = l_Lean_Meta_simpTargetStar(v_mvarId_1334_, v_a_1903_, v___x_1898_, v___x_1895_, v___x_1904_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_2004_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_2004_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_2004_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_fst_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_2002_; 
v_fst_1910_ = lean_ctor_get(v_a_1906_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_a_1906_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; 
v_unused_2003_ = lean_ctor_get(v_a_1906_, 1);
lean_dec(v_unused_2003_);
v___x_1912_ = v_a_1906_;
v_isShared_1913_ = v_isSharedCheck_2002_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_fst_1910_);
lean_dec(v_a_1906_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_2002_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
switch(lean_obj_tag(v_fst_1910_))
{
case 0:
{
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_box(0);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1914_);
v___x_1916_ = v___x_1908_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_del_object(v___x_1908_);
v___x_1918_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1919_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1918_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1919_;
}
}
case 1:
{
lean_object* v___x_1920_; 
lean_del_object(v___x_1908_);
lean_inc(v_declName_1333_);
lean_inc(v_mvarId_1334_);
v___x_1920_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1334_, v_declName_1333_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref(v___x_1920_);
if (lean_obj_tag(v_a_1921_) == 1)
{
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1922_; 
v_val_1922_ = lean_ctor_get(v_a_1921_, 0);
lean_inc(v_val_1922_);
lean_dec_ref(v_a_1921_);
v_mvarId_1334_ = v_val_1922_;
goto _start;
}
else
{
lean_object* v_val_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_val_1924_ = lean_ctor_get(v_a_1921_, 0);
lean_inc(v_val_1924_);
lean_dec_ref(v_a_1921_);
v___x_1925_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1926_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1925_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_dec_ref(v___x_1926_);
v_mvarId_1334_ = v_val_1924_;
goto _start;
}
else
{
lean_dec(v_val_1924_);
lean_dec(v_declName_1333_);
return v___x_1926_;
}
}
}
else
{
lean_object* v___x_1928_; 
lean_dec(v_a_1921_);
lean_inc(v_mvarId_1334_);
v___x_1928_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1979_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1931_ = v___x_1928_;
v_isShared_1932_ = v_isSharedCheck_1979_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1928_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1979_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
if (lean_obj_tag(v_a_1929_) == 1)
{
lean_object* v_val_1933_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; 
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1334_);
v_val_1933_ = lean_ctor_get(v_a_1929_, 0);
lean_inc(v_val_1933_);
lean_dec_ref(v_a_1929_);
if (v___x_1534_ == 0)
{
v___y_1935_ = v_a_1335_;
v___y_1936_ = v_a_1336_;
v___y_1937_ = v_a_1337_;
v___y_1938_ = v_a_1338_;
goto v___jp_1934_;
}
else
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1956_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1955_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_dec_ref(v___x_1956_);
v___y_1935_ = v_a_1335_;
v___y_1936_ = v_a_1336_;
v___y_1937_ = v_a_1337_;
v___y_1938_ = v_a_1338_;
goto v___jp_1934_;
}
else
{
lean_dec(v_val_1933_);
lean_del_object(v___x_1931_);
lean_dec(v_declName_1333_);
return v___x_1956_;
}
}
v___jp_1934_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1939_ = lean_array_get_size(v_val_1933_);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_nat_dec_lt(v___x_1897_, v___x_1939_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1943_; 
lean_dec(v_val_1933_);
lean_dec(v_declName_1333_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1940_);
v___x_1943_ = v___x_1931_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1940_);
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
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_le(v___x_1939_, v___x_1939_);
if (v___x_1945_ == 0)
{
if (v___x_1941_ == 0)
{
lean_object* v___x_1947_; 
lean_dec(v_val_1933_);
lean_dec(v_declName_1333_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1940_);
v___x_1947_ = v___x_1931_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1940_);
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
size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
lean_del_object(v___x_1931_);
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = lean_usize_of_nat(v___x_1939_);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1333_, v_val_1933_, v___x_1949_, v___x_1950_, v___x_1940_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v_val_1933_);
return v___x_1951_;
}
}
else
{
size_t v___x_1952_; size_t v___x_1953_; lean_object* v___x_1954_; 
lean_del_object(v___x_1931_);
v___x_1952_ = ((size_t)0ULL);
v___x_1953_ = lean_usize_of_nat(v___x_1939_);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_1333_, v_val_1933_, v___x_1952_, v___x_1953_, v___x_1940_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v_val_1933_);
return v___x_1954_;
}
}
}
}
else
{
lean_object* v___x_1957_; 
lean_del_object(v___x_1931_);
lean_dec(v_a_1929_);
lean_inc(v_mvarId_1334_);
v___x_1957_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1334_, v_hasTrace_1347_, v_hasTrace_1347_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1957_);
if (lean_obj_tag(v_a_1958_) == 1)
{
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1959_; lean_object* v___x_1960_; 
v_val_1959_ = lean_ctor_get(v_a_1958_, 0);
lean_inc(v_val_1959_);
lean_dec_ref(v_a_1958_);
v___x_1960_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1333_, v_val_1959_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1960_;
}
else
{
lean_object* v_val_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_val_1961_ = lean_ctor_get(v_a_1958_, 0);
lean_inc(v_val_1961_);
lean_dec_ref(v_a_1958_);
v___x_1962_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1963_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1962_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v___x_1963_);
v___x_1964_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1333_, v_val_1961_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1964_;
}
else
{
lean_dec(v_val_1961_);
lean_dec(v_declName_1333_);
return v___x_1963_;
}
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1968_; 
lean_dec(v_a_1958_);
lean_dec(v_declName_1333_);
v___x_1965_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_mvarId_1334_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set_tag(v___x_1912_, 7);
lean_ctor_set(v___x_1912_, 1, v___x_1966_);
lean_ctor_set(v___x_1912_, 0, v___x_1965_);
v___x_1968_ = v___x_1912_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v___x_1966_);
v___x_1968_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1968_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1969_;
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1971_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1957_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1957_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1980_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1928_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1928_);
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
lean_del_object(v___x_1912_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1988_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1920_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1920_);
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
default: 
{
lean_del_object(v___x_1912_);
lean_del_object(v___x_1908_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_mvarId_1996_; 
v_mvarId_1996_ = lean_ctor_get(v_fst_1910_, 0);
lean_inc(v_mvarId_1996_);
lean_dec_ref(v_fst_1910_);
v_mvarId_1334_ = v_mvarId_1996_;
goto _start;
}
else
{
lean_object* v_mvarId_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_mvarId_1998_ = lean_ctor_get(v_fst_1910_, 0);
lean_inc(v_mvarId_1998_);
lean_dec_ref(v_fst_1910_);
v___x_1999_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_2000_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1999_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_dec_ref(v___x_2000_);
v_mvarId_1334_ = v_mvarId_1998_;
goto _start;
}
else
{
lean_dec(v_mvarId_1998_);
lean_dec(v_declName_1333_);
return v___x_2000_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_2005_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1905_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1905_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_2013_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1902_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1902_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2028_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_2021_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1884_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_1884_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2026_; 
if (v_isShared_2024_ == 0)
{
v___x_2026_ = v___x_2023_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_2029_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_1876_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_1876_);
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
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_2037_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1868_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1868_);
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
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
goto v___jp_1343_;
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_2046_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_2045_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_dec_ref(v___x_2046_);
goto v___jp_1343_;
}
else
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_2047_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_1865_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_1865_);
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
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
goto v___jp_1340_;
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_2056_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_2055_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_dec_ref(v___x_2056_);
goto v___jp_1340_;
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
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_2057_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_1862_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_1862_);
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
goto v___jp_1594_;
}
}
else
{
goto v___jp_1594_;
}
v___jp_1535_:
{
lean_object* v___x_1539_; double v___x_1540_; double v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1539_ = lean_io_get_num_heartbeats();
v___x_1540_ = lean_float_of_nat(v___y_1536_);
v___x_1541_ = lean_float_of_nat(v___x_1539_);
v___x_1542_ = lean_box_float(v___x_1540_);
v___x_1543_ = lean_box_float(v___x_1541_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v_a_1538_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1531_, v_hasTrace_1347_, v___x_1532_, v_options_1346_, v___x_1534_, v___y_1537_, v___f_1530_, v___x_1545_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1546_;
}
v___jp_1547_:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v_a_1550_);
v___y_1536_ = v___y_1548_;
v___y_1537_ = v___y_1549_;
v_a_1538_ = v___x_1551_;
goto v___jp_1535_;
}
v___jp_1552_:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_a_1555_);
v___y_1536_ = v___y_1553_;
v___y_1537_ = v___y_1554_;
v_a_1538_ = v___x_1556_;
goto v___jp_1535_;
}
v___jp_1557_:
{
if (lean_obj_tag(v___y_1560_) == 0)
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___y_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___y_1560_);
v___y_1553_ = v___y_1558_;
v___y_1554_ = v___y_1559_;
v_a_1555_ = v_a_1561_;
goto v___jp_1552_;
}
else
{
lean_object* v_a_1562_; 
v_a_1562_ = lean_ctor_get(v___y_1560_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___y_1560_);
v___y_1548_ = v___y_1558_;
v___y_1549_ = v___y_1559_;
v_a_1550_ = v_a_1562_;
goto v___jp_1547_;
}
}
v___jp_1563_:
{
lean_object* v___x_1567_; double v___x_1568_; double v___x_1569_; double v___x_1570_; double v___x_1571_; double v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1567_ = lean_io_mono_nanos_now();
v___x_1568_ = lean_float_of_nat(v___y_1564_);
v___x_1569_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_1570_ = lean_float_div(v___x_1568_, v___x_1569_);
v___x_1571_ = lean_float_of_nat(v___x_1567_);
v___x_1572_ = lean_float_div(v___x_1571_, v___x_1569_);
v___x_1573_ = lean_box_float(v___x_1570_);
v___x_1574_ = lean_box_float(v___x_1572_);
v___x_1575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1576_, 0, v_a_1566_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_1531_, v_hasTrace_1347_, v___x_1532_, v_options_1346_, v___x_1534_, v___y_1565_, v___f_1530_, v___x_1576_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
return v___x_1577_;
}
v___jp_1578_:
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1582_, 0, v_a_1581_);
v___y_1564_ = v___y_1579_;
v___y_1565_ = v___y_1580_;
v_a_1566_ = v___x_1582_;
goto v___jp_1563_;
}
v___jp_1583_:
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v_a_1586_);
v___y_1564_ = v___y_1584_;
v___y_1565_ = v___y_1585_;
v_a_1566_ = v___x_1587_;
goto v___jp_1563_;
}
v___jp_1588_:
{
if (lean_obj_tag(v___y_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___y_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___y_1591_);
v___y_1579_ = v___y_1589_;
v___y_1580_ = v___y_1590_;
v_a_1581_ = v_a_1592_;
goto v___jp_1578_;
}
else
{
lean_object* v_a_1593_; 
v_a_1593_ = lean_ctor_get(v___y_1591_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___y_1591_);
v___y_1584_ = v___y_1589_;
v___y_1585_ = v___y_1590_;
v_a_1586_ = v_a_1593_;
goto v___jp_1583_;
}
}
v___jp_1594_:
{
lean_object* v___x_1595_; 
v___x_1595_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_1338_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v___x_1597_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1598_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_1346_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_io_mono_nanos_now();
lean_inc(v_mvarId_1334_);
v___x_1600_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; uint8_t v___x_1602_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = lean_unbox(v_a_1601_);
lean_dec(v_a_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_inc(v_mvarId_1334_);
v___x_1603_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; uint8_t v___x_1605_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = lean_unbox(v_a_1604_);
lean_dec(v_a_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_inc(v_mvarId_1334_);
v___x_1606_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref(v___x_1606_);
if (lean_obj_tag(v_a_1607_) == 1)
{
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1608_; lean_object* v___x_1609_; 
v_val_1608_ = lean_ctor_get(v_a_1607_, 0);
lean_inc(v_val_1608_);
lean_dec_ref(v_a_1607_);
v___x_1609_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1608_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1609_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v_val_1610_ = lean_ctor_get(v_a_1607_, 0);
lean_inc(v_val_1610_);
lean_dec_ref(v_a_1607_);
v___x_1611_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1612_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1611_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref(v___x_1612_);
v___x_1613_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1610_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1613_;
goto v___jp_1588_;
}
else
{
lean_dec(v_val_1610_);
lean_dec(v_declName_1333_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1612_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v___x_1614_; 
lean_dec(v_a_1607_);
lean_inc(v_mvarId_1334_);
v___x_1614_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
if (lean_obj_tag(v_a_1615_) == 1)
{
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1616_; lean_object* v___x_1617_; 
v_val_1616_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref(v_a_1615_);
v___x_1617_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1616_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1617_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v_val_1618_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_val_1618_);
lean_dec_ref(v_a_1615_);
v___x_1619_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1620_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1619_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v___x_1621_; 
lean_dec_ref(v___x_1620_);
v___x_1621_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1618_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1621_;
goto v___jp_1588_;
}
else
{
lean_dec(v_val_1618_);
lean_dec(v_declName_1333_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1620_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v___x_1622_; 
lean_dec(v_a_1615_);
lean_inc(v_mvarId_1334_);
v___x_1622_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1334_, v_hasTrace_1347_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
if (lean_obj_tag(v_a_1623_) == 1)
{
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1624_; lean_object* v___x_1625_; 
v_val_1624_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v_a_1623_);
v___x_1625_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1624_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1625_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_val_1626_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_val_1626_);
lean_dec_ref(v_a_1623_);
v___x_1627_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1628_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1627_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v___x_1629_; 
lean_dec_ref(v___x_1628_);
v___x_1629_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1626_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1629_;
goto v___jp_1588_;
}
else
{
lean_dec(v_val_1626_);
lean_dec(v_declName_1333_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1628_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec(v_a_1623_);
v___x_1630_ = lean_unsigned_to_nat(100000u);
v___x_1631_ = lean_unsigned_to_nat(2u);
v___x_1632_ = 0;
v___x_1633_ = lean_box(0);
v___x_1634_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1634_, 0, v___x_1630_);
lean_ctor_set(v___x_1634_, 1, v___x_1631_);
lean_ctor_set(v___x_1634_, 2, v___x_1633_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 1, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 2, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 3, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 4, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 5, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 6, v___x_1632_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 7, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 8, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 9, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 10, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 11, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 12, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 13, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 14, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 15, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 16, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 17, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 18, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 19, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 20, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 21, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 22, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 23, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 24, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 25, v_hasTrace_1347_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 26, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 27, v___x_1598_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*3 + 28, v___x_1598_);
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1637_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1638_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1639_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*2, v_hasTrace_1347_);
v___x_1640_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1634_, v___x_1636_, v___x_1639_, v_a_1335_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1640_);
v___x_1642_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1334_);
v___x_1643_ = l_Lean_Meta_simpTargetStar(v_mvarId_1334_, v_a_1641_, v___x_1636_, v___x_1633_, v___x_1642_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v_fst_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1699_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1643_);
v_fst_1645_ = lean_ctor_get(v_a_1644_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_a_1644_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; 
v_unused_1700_ = lean_ctor_get(v_a_1644_, 1);
lean_dec(v_unused_1700_);
v___x_1647_ = v_a_1644_;
v_isShared_1648_ = v_isSharedCheck_1699_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_fst_1645_);
lean_dec(v_a_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1699_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
switch(lean_obj_tag(v_fst_1645_))
{
case 0:
{
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_box(0);
v___y_1579_ = v___x_1599_;
v___y_1580_ = v_a_1596_;
v_a_1581_ = v___x_1649_;
goto v___jp_1578_;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1651_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1650_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1651_;
goto v___jp_1588_;
}
}
case 1:
{
lean_object* v___x_1652_; 
lean_inc(v_declName_1333_);
lean_inc(v_mvarId_1334_);
v___x_1652_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1334_, v_declName_1333_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
if (lean_obj_tag(v_a_1653_) == 1)
{
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1654_; lean_object* v___x_1655_; 
v_val_1654_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_val_1654_);
lean_dec_ref(v_a_1653_);
v___x_1655_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1654_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1655_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_val_1656_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_val_1656_);
lean_dec_ref(v_a_1653_);
v___x_1657_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1658_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1657_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v___x_1659_; 
lean_dec_ref(v___x_1658_);
v___x_1659_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1656_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1659_;
goto v___jp_1588_;
}
else
{
lean_dec(v_val_1656_);
lean_dec(v_declName_1333_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1658_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v___x_1660_; 
lean_dec(v_a_1653_);
lean_inc(v_mvarId_1334_);
v___x_1660_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; 
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v___x_1660_);
if (lean_obj_tag(v_a_1661_) == 1)
{
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_val_1662_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_val_1662_);
lean_dec_ref(v_a_1661_);
v___x_1663_ = lean_box(0);
v___x_1664_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1662_, v___x_1635_, v_declName_1333_, v___x_1663_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_val_1662_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1664_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v_val_1665_ = lean_ctor_get(v_a_1661_, 0);
lean_inc(v_val_1665_);
lean_dec_ref(v_a_1661_);
v___x_1666_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1667_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1666_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1665_, v___x_1635_, v_declName_1333_, v_a_1668_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_val_1665_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1669_;
goto v___jp_1588_;
}
else
{
lean_dec(v_val_1665_);
lean_dec(v_declName_1333_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1667_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v___x_1670_; 
lean_dec(v_a_1661_);
lean_inc(v_mvarId_1334_);
v___x_1670_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1334_, v_hasTrace_1347_, v_hasTrace_1347_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1689_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1673_ = v___x_1670_;
v_isShared_1674_ = v_isSharedCheck_1689_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1670_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1689_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
if (lean_obj_tag(v_a_1671_) == 1)
{
lean_del_object(v___x_1673_);
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1675_; lean_object* v___x_1676_; 
v_val_1675_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_val_1675_);
lean_dec_ref(v_a_1671_);
v___x_1676_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1333_, v_val_1675_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1676_;
goto v___jp_1588_;
}
else
{
lean_object* v_val_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_val_1677_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_val_1677_);
lean_dec_ref(v_a_1671_);
v___x_1678_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1679_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1678_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v___x_1680_; 
lean_dec_ref(v___x_1679_);
v___x_1680_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1333_, v_val_1677_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1680_;
goto v___jp_1588_;
}
else
{
lean_dec(v_val_1677_);
lean_dec(v_declName_1333_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1679_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
lean_dec(v_a_1671_);
lean_dec(v_declName_1333_);
v___x_1681_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 1);
lean_ctor_set(v___x_1673_, 0, v_mvarId_1334_);
v___x_1683_ = v___x_1673_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_mvarId_1334_);
v___x_1683_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1685_; 
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 7);
lean_ctor_set(v___x_1647_, 1, v___x_1683_);
lean_ctor_set(v___x_1647_, 0, v___x_1681_);
v___x_1685_ = v___x_1647_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1685_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1686_;
goto v___jp_1588_;
}
}
}
}
}
else
{
lean_object* v_a_1690_; 
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1690_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1670_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1690_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v_a_1691_; 
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1691_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1660_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1691_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v_a_1692_; 
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1692_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1692_);
lean_dec_ref(v___x_1652_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1692_;
goto v___jp_1583_;
}
}
default: 
{
lean_del_object(v___x_1647_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_mvarId_1693_; lean_object* v___x_1694_; 
v_mvarId_1693_ = lean_ctor_get(v_fst_1645_, 0);
lean_inc(v_mvarId_1693_);
lean_dec_ref(v_fst_1645_);
v___x_1694_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_mvarId_1693_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1694_;
goto v___jp_1588_;
}
else
{
lean_object* v_mvarId_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_mvarId_1695_ = lean_ctor_get(v_fst_1645_, 0);
lean_inc(v_mvarId_1695_);
lean_dec_ref(v_fst_1645_);
v___x_1696_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1697_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1696_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v___x_1698_; 
lean_dec_ref(v___x_1697_);
v___x_1698_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_mvarId_1695_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1698_;
goto v___jp_1588_;
}
else
{
lean_dec(v_mvarId_1695_);
lean_dec(v_declName_1333_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1697_;
goto v___jp_1588_;
}
}
}
}
}
}
else
{
lean_object* v_a_1701_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1701_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1701_);
lean_dec_ref(v___x_1643_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1701_;
goto v___jp_1583_;
}
}
else
{
lean_object* v_a_1702_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1702_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1640_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1702_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v_a_1703_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1703_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1622_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1703_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v_a_1704_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1704_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1614_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1704_;
goto v___jp_1583_;
}
}
}
else
{
lean_object* v_a_1705_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1705_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1705_);
lean_dec_ref(v___x_1606_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1705_;
goto v___jp_1583_;
}
}
else
{
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_box(0);
v___x_1707_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1706_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1707_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1709_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1708_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1711_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref(v___x_1709_);
v___x_1711_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1710_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1711_;
goto v___jp_1588_;
}
else
{
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1709_;
goto v___jp_1588_;
}
}
}
}
else
{
lean_object* v_a_1712_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1712_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1712_);
lean_dec_ref(v___x_1603_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1712_;
goto v___jp_1583_;
}
}
else
{
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1713_ = lean_box(0);
v___x_1714_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1713_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1714_;
goto v___jp_1588_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1716_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1715_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref(v___x_1716_);
v___x_1718_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1717_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1718_;
goto v___jp_1588_;
}
else
{
v___y_1589_ = v___x_1599_;
v___y_1590_ = v_a_1596_;
v___y_1591_ = v___x_1716_;
goto v___jp_1588_;
}
}
}
}
else
{
lean_object* v_a_1719_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1719_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1600_);
v___y_1584_ = v___x_1599_;
v___y_1585_ = v_a_1596_;
v_a_1586_ = v_a_1719_;
goto v___jp_1583_;
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_io_get_num_heartbeats();
lean_inc(v_mvarId_1334_);
v___x_1721_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; uint8_t v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref(v___x_1721_);
v___x_1723_ = lean_unbox(v_a_1722_);
lean_dec(v_a_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_inc(v_mvarId_1334_);
v___x_1724_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; uint8_t v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = lean_unbox(v_a_1725_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
lean_inc(v_mvarId_1334_);
v___x_1727_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1727_);
if (lean_obj_tag(v_a_1728_) == 1)
{
lean_dec(v_a_1725_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1729_; lean_object* v___x_1730_; 
v_val_1729_ = lean_ctor_get(v_a_1728_, 0);
lean_inc(v_val_1729_);
lean_dec_ref(v_a_1728_);
v___x_1730_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1729_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1730_;
goto v___jp_1557_;
}
else
{
lean_object* v_val_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_val_1731_ = lean_ctor_get(v_a_1728_, 0);
lean_inc(v_val_1731_);
lean_dec_ref(v_a_1728_);
v___x_1732_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__23);
v___x_1733_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1732_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref(v___x_1733_);
v___x_1734_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1731_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1734_;
goto v___jp_1557_;
}
else
{
lean_dec(v_val_1731_);
lean_dec(v_declName_1333_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1733_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1735_; 
lean_dec(v_a_1728_);
lean_inc(v_mvarId_1334_);
v___x_1735_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
if (lean_obj_tag(v_a_1736_) == 1)
{
lean_dec(v_a_1725_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1737_; lean_object* v___x_1738_; 
v_val_1737_ = lean_ctor_get(v_a_1736_, 0);
lean_inc(v_val_1737_);
lean_dec_ref(v_a_1736_);
v___x_1738_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1737_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1738_;
goto v___jp_1557_;
}
else
{
lean_object* v_val_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_val_1739_ = lean_ctor_get(v_a_1736_, 0);
lean_inc(v_val_1739_);
lean_dec_ref(v_a_1736_);
v___x_1740_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__25);
v___x_1741_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1740_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1742_; 
lean_dec_ref(v___x_1741_);
v___x_1742_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1739_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1742_;
goto v___jp_1557_;
}
else
{
lean_dec(v_val_1739_);
lean_dec(v_declName_1333_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1741_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1743_; 
lean_dec(v_a_1736_);
lean_inc(v_mvarId_1334_);
v___x_1743_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_1334_, v___x_1598_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
if (lean_obj_tag(v_a_1744_) == 1)
{
lean_dec(v_a_1725_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1745_; lean_object* v___x_1746_; 
v_val_1745_ = lean_ctor_get(v_a_1744_, 0);
lean_inc(v_val_1745_);
lean_dec_ref(v_a_1744_);
v___x_1746_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1745_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1746_;
goto v___jp_1557_;
}
else
{
lean_object* v_val_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v_val_1747_ = lean_ctor_get(v_a_1744_, 0);
lean_inc(v_val_1747_);
lean_dec_ref(v_a_1744_);
v___x_1748_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__27);
v___x_1749_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1748_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v___x_1750_; 
lean_dec_ref(v___x_1749_);
v___x_1750_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1747_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1750_;
goto v___jp_1557_;
}
else
{
lean_dec(v_val_1747_);
lean_dec(v_declName_1333_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1749_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; uint8_t v___x_1757_; uint8_t v___x_1758_; uint8_t v___x_1759_; uint8_t v___x_1760_; uint8_t v___x_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; uint8_t v___x_1764_; uint8_t v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v_a_1744_);
v___x_1751_ = lean_unsigned_to_nat(100000u);
v___x_1752_ = lean_unsigned_to_nat(2u);
v___x_1753_ = 0;
v___x_1754_ = lean_box(0);
v___x_1755_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_1755_, 0, v___x_1751_);
lean_ctor_set(v___x_1755_, 1, v___x_1752_);
lean_ctor_set(v___x_1755_, 2, v___x_1754_);
v___x_1756_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3, v___x_1756_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 1, v___x_1598_);
v___x_1757_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 2, v___x_1757_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 3, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 4, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 5, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 6, v___x_1753_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 7, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 8, v___x_1598_);
v___x_1758_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 9, v___x_1758_);
v___x_1759_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 10, v___x_1759_);
v___x_1760_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 11, v___x_1760_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 12, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 13, v___x_1598_);
v___x_1761_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 14, v___x_1761_);
v___x_1762_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 15, v___x_1762_);
v___x_1763_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 16, v___x_1763_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 17, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 18, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 19, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 20, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 21, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 22, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 23, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 24, v___x_1598_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 25, v___x_1598_);
v___x_1764_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 26, v___x_1764_);
v___x_1765_ = lean_unbox(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 27, v___x_1765_);
v___x_1766_ = lean_unbox(v_a_1725_);
lean_dec(v_a_1725_);
lean_ctor_set_uint8(v___x_1755_, sizeof(void*)*3 + 28, v___x_1766_);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__0));
v___x_1769_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__2);
v___x_1770_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__4);
v___x_1771_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1771_, 0, v___x_1769_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*2, v___x_1598_);
v___x_1772_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_1755_, v___x_1768_, v___x_1771_, v_a_1335_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__10);
lean_inc(v_mvarId_1334_);
v___x_1775_ = l_Lean_Meta_simpTargetStar(v_mvarId_1334_, v_a_1773_, v___x_1768_, v___x_1754_, v___x_1774_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_fst_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1831_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v_fst_1777_ = lean_ctor_get(v_a_1776_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_a_1776_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v_a_1776_, 1);
lean_dec(v_unused_1832_);
v___x_1779_ = v_a_1776_;
v_isShared_1780_ = v_isSharedCheck_1831_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_fst_1777_);
lean_dec(v_a_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1831_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
switch(lean_obj_tag(v_fst_1777_))
{
case 0:
{
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_box(0);
v___y_1553_ = v___x_1720_;
v___y_1554_ = v_a_1596_;
v_a_1555_ = v___x_1781_;
goto v___jp_1552_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__29);
v___x_1783_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1782_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1783_;
goto v___jp_1557_;
}
}
case 1:
{
lean_object* v___x_1784_; 
lean_inc(v_declName_1333_);
lean_inc(v_mvarId_1334_);
v___x_1784_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f(v_mvarId_1334_, v_declName_1333_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
if (lean_obj_tag(v_a_1785_) == 1)
{
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1786_; lean_object* v___x_1787_; 
v_val_1786_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1786_);
lean_dec_ref(v_a_1785_);
v___x_1787_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1786_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1787_;
goto v___jp_1557_;
}
else
{
lean_object* v_val_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_val_1788_ = lean_ctor_get(v_a_1785_, 0);
lean_inc(v_val_1788_);
lean_dec_ref(v_a_1785_);
v___x_1789_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__31);
v___x_1790_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1789_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v___x_1790_);
v___x_1791_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_val_1788_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1791_;
goto v___jp_1557_;
}
else
{
lean_dec(v_val_1788_);
lean_dec(v_declName_1333_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1790_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1792_; 
lean_dec(v_a_1785_);
lean_inc(v_mvarId_1334_);
v___x_1792_ = l_Lean_Meta_casesOnStuckLHS_x3f(v_mvarId_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref(v___x_1792_);
if (lean_obj_tag(v_a_1793_) == 1)
{
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_val_1794_ = lean_ctor_get(v_a_1793_, 0);
lean_inc(v_val_1794_);
lean_dec_ref(v_a_1793_);
v___x_1795_ = lean_box(0);
v___x_1796_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1794_, v___x_1767_, v_declName_1333_, v___x_1795_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_val_1794_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1796_;
goto v___jp_1557_;
}
else
{
lean_object* v_val_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_val_1797_ = lean_ctor_get(v_a_1793_, 0);
lean_inc(v_val_1797_);
lean_dec_ref(v_a_1793_);
v___x_1798_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__33);
v___x_1799_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1798_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_a_1800_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_1797_, v___x_1767_, v_declName_1333_, v_a_1800_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_val_1797_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1801_;
goto v___jp_1557_;
}
else
{
lean_dec(v_val_1797_);
lean_dec(v_declName_1333_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1799_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1802_; 
lean_dec(v_a_1793_);
lean_inc(v_mvarId_1334_);
v___x_1802_ = l_Lean_Meta_splitTarget_x3f(v_mvarId_1334_, v___x_1598_, v___x_1598_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1821_; 
v_a_1803_ = lean_ctor_get(v___x_1802_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1805_ = v___x_1802_;
v_isShared_1806_ = v_isSharedCheck_1821_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1821_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
if (lean_obj_tag(v_a_1803_) == 1)
{
lean_del_object(v___x_1805_);
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_val_1807_; lean_object* v___x_1808_; 
v_val_1807_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_val_1807_);
lean_dec_ref(v_a_1803_);
v___x_1808_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1333_, v_val_1807_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1808_;
goto v___jp_1557_;
}
else
{
lean_object* v_val_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_val_1809_ = lean_ctor_get(v_a_1803_, 0);
lean_inc(v_val_1809_);
lean_dec_ref(v_a_1803_);
v___x_1810_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__35);
v___x_1811_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1810_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v___x_1812_; 
lean_dec_ref(v___x_1811_);
v___x_1812_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_1333_, v_val_1809_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1812_;
goto v___jp_1557_;
}
else
{
lean_dec(v_val_1809_);
lean_dec(v_declName_1333_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1811_;
goto v___jp_1557_;
}
}
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
lean_dec(v_a_1803_);
lean_dec(v_declName_1333_);
v___x_1813_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__12);
if (v_isShared_1806_ == 0)
{
lean_ctor_set_tag(v___x_1805_, 1);
lean_ctor_set(v___x_1805_, 0, v_mvarId_1334_);
v___x_1815_ = v___x_1805_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_mvarId_1334_);
v___x_1815_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1817_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set_tag(v___x_1779_, 7);
lean_ctor_set(v___x_1779_, 1, v___x_1815_);
lean_ctor_set(v___x_1779_, 0, v___x_1813_);
v___x_1817_ = v___x_1779_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_1817_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1818_;
goto v___jp_1557_;
}
}
}
}
}
else
{
lean_object* v_a_1822_; 
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1822_ = lean_ctor_get(v___x_1802_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1802_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1822_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_1823_; 
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1823_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1792_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1823_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_1824_; 
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1824_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1784_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1824_;
goto v___jp_1547_;
}
}
default: 
{
lean_del_object(v___x_1779_);
lean_dec(v_mvarId_1334_);
if (v___x_1534_ == 0)
{
lean_object* v_mvarId_1825_; lean_object* v___x_1826_; 
v_mvarId_1825_ = lean_ctor_get(v_fst_1777_, 0);
lean_inc(v_mvarId_1825_);
lean_dec_ref(v_fst_1777_);
v___x_1826_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_mvarId_1825_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1826_;
goto v___jp_1557_;
}
else
{
lean_object* v_mvarId_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_mvarId_1827_ = lean_ctor_get(v_fst_1777_, 0);
lean_inc(v_mvarId_1827_);
lean_dec_ref(v_fst_1777_);
v___x_1828_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__37);
v___x_1829_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1828_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1830_; 
lean_dec_ref(v___x_1829_);
v___x_1830_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_1333_, v_mvarId_1827_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1830_;
goto v___jp_1557_;
}
else
{
lean_dec(v_mvarId_1827_);
lean_dec(v_declName_1333_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1829_;
goto v___jp_1557_;
}
}
}
}
}
}
else
{
lean_object* v_a_1833_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1833_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1833_);
lean_dec_ref(v___x_1775_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1833_;
goto v___jp_1547_;
}
}
else
{
lean_object* v_a_1834_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1834_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1772_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1834_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_1835_; 
lean_dec(v_a_1725_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1835_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1743_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1835_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_1836_; 
lean_dec(v_a_1725_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1836_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1735_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1836_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_1837_; 
lean_dec(v_a_1725_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1837_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1727_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1837_;
goto v___jp_1547_;
}
}
else
{
lean_dec(v_a_1725_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_box(0);
v___x_1839_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1838_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1839_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__39);
v___x_1841_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1840_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1841_);
v___x_1843_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1842_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1843_;
goto v___jp_1557_;
}
else
{
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1841_;
goto v___jp_1557_;
}
}
}
}
else
{
lean_object* v_a_1844_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1844_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1724_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1844_;
goto v___jp_1547_;
}
}
else
{
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_box(0);
v___x_1846_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v___x_1845_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1846_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__41);
v___x_1848_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_1531_, v___x_1847_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__1(v_a_1849_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1850_;
goto v___jp_1557_;
}
else
{
v___y_1558_ = v___x_1720_;
v___y_1559_ = v_a_1596_;
v___y_1560_ = v___x_1848_;
goto v___jp_1557_;
}
}
}
}
else
{
lean_object* v_a_1851_; 
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1851_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v___x_1721_);
v___y_1548_ = v___x_1720_;
v___y_1549_ = v_a_1596_;
v_a_1550_ = v_a_1851_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v___f_1530_);
lean_dec(v_mvarId_1334_);
lean_dec(v_declName_1333_);
v_a_1852_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1595_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1595_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
v___jp_1340_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
return v___x_1342_;
}
v___jp_1343_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(lean_object* v_declName_2065_, lean_object* v_as_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
if (lean_obj_tag(v_as_2066_) == 0)
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v_declName_2065_);
v___x_2072_ = lean_box(0);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
return v___x_2073_;
}
else
{
lean_object* v_head_2074_; lean_object* v_tail_2075_; lean_object* v___x_2076_; 
v_head_2074_ = lean_ctor_get(v_as_2066_, 0);
lean_inc(v_head_2074_);
v_tail_2075_ = lean_ctor_get(v_as_2066_, 1);
lean_inc(v_tail_2075_);
lean_dec_ref(v_as_2066_);
lean_inc(v_declName_2065_);
v___x_2076_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2065_, v_head_2074_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_dec_ref(v___x_2076_);
v_as_2066_ = v_tail_2075_;
goto _start;
}
else
{
lean_dec(v_tail_2075_);
lean_dec(v_declName_2065_);
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2___boxed(lean_object* v_declName_2078_, lean_object* v_as_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_List_forM___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__2(v_declName_2078_, v_as_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* v_declName_2086_, lean_object* v_as_2087_, lean_object* v_i_2088_, lean_object* v_stop_2089_, lean_object* v_b_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
size_t v_i_boxed_2096_; size_t v_stop_boxed_2097_; lean_object* v_res_2098_; 
v_i_boxed_2096_ = lean_unbox_usize(v_i_2088_);
lean_dec(v_i_2088_);
v_stop_boxed_2097_ = lean_unbox_usize(v_stop_2089_);
lean_dec(v_stop_2089_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(v_declName_2086_, v_as_2087_, v_i_boxed_2096_, v_stop_boxed_2097_, v_b_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec_ref(v_as_2087_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5___boxed(lean_object* v_val_2099_, lean_object* v___x_2100_, lean_object* v_declName_2101_, lean_object* v_____r_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___lam__5(v_val_2099_, v___x_2100_, v_declName_2101_, v_____r_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___x_2100_);
lean_dec_ref(v_val_2099_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___boxed(lean_object* v_declName_2109_, lean_object* v_mvarId_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2109_, v_mvarId_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(lean_object* v_00_u03b1_2117_, lean_object* v_x_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_x_2118_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2125_, lean_object* v_x_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7(v_00_u03b1_2125_, v_x_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(lean_object* v_constName_2133_, uint8_t v_skipRealize_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; lean_object* v_env_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2137_ = lean_st_ref_get(v___y_2135_);
v_env_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc_ref(v_env_2138_);
lean_dec(v___x_2137_);
v___x_2139_ = l_Lean_Environment_contains(v_env_2138_, v_constName_2133_, v_skipRealize_2134_);
v___x_2140_ = lean_box(v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg___boxed(lean_object* v_constName_2142_, lean_object* v_skipRealize_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
uint8_t v_skipRealize_boxed_2146_; lean_object* v_res_2147_; 
v_skipRealize_boxed_2146_ = lean_unbox(v_skipRealize_2143_);
v_res_2147_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2142_, v_skipRealize_boxed_2146_, v___y_2144_);
lean_dec(v___y_2144_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(lean_object* v_constName_2148_, uint8_t v_skipRealize_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v_constName_2148_, v_skipRealize_2149_, v___y_2153_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___boxed(lean_object* v_constName_2156_, lean_object* v_skipRealize_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v_skipRealize_boxed_2163_; lean_object* v_res_2164_; 
v_skipRealize_boxed_2163_ = lean_unbox(v_skipRealize_2157_);
v_res_2164_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0(v_constName_2156_, v_skipRealize_boxed_2163_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(lean_object* v_snd_2165_, lean_object* v___x_2166_, lean_object* v___x_2167_, lean_object* v_snd_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
lean_inc_ref(v_snd_2165_);
v___x_2174_ = l_Lean_Meta_mkCongrArg(v_snd_2165_, v___x_2166_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = l_Lean_Expr_app___override(v_snd_2165_, v___x_2167_);
v___x_2177_ = l_Lean_MVarId_replaceTargetEq(v_snd_2168_, v___x_2176_, v_a_2175_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2177_;
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_snd_2168_);
lean_dec_ref(v___x_2167_);
lean_dec_ref(v_snd_2165_);
v_a_2178_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2174_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2174_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed(lean_object* v_snd_2186_, lean_object* v___x_2187_, lean_object* v___x_2188_, lean_object* v_snd_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0(v_snd_2186_, v___x_2187_, v___x_2188_, v_snd_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2195_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__3));
v___x_2202_ = l_Lean_stringToMessageData(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__5));
v___x_2205_ = l_Lean_stringToMessageData(v___x_2204_);
return v___x_2205_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__7));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__9));
v___x_2211_ = l_Lean_stringToMessageData(v___x_2210_);
return v___x_2211_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__11));
v___x_2214_ = l_Lean_stringToMessageData(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__13));
v___x_2217_ = l_Lean_stringToMessageData(v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(lean_object* v_mvarId_2218_, lean_object* v___x_2219_, lean_object* v_cls_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
lean_inc(v_mvarId_2218_);
v___x_2226_ = l_Lean_MVarId_getType(v_mvarId_2218_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref(v___x_2226_);
v___x_2228_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS(v_a_2227_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v_fst_2230_; lean_object* v_snd_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2384_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref(v___x_2228_);
v_fst_2230_ = lean_ctor_get(v_a_2229_, 0);
v_snd_2231_ = lean_ctor_get(v_a_2229_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_a_2229_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2233_ = v_a_2229_;
v_isShared_2234_ = v_isSharedCheck_2384_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_snd_2231_);
lean_inc(v_fst_2230_);
lean_dec(v_a_2229_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2384_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2383_; 
v___x_2235_ = l_Lean_Expr_getAppFn(v_fst_2230_);
v___x_2236_ = l_Lean_Expr_constName_x21(v___x_2235_);
v___x_2237_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__0));
v___x_2238_ = l_Lean_Name_str___override(v___x_2236_, v___x_2237_);
v___x_2239_ = 1;
lean_inc(v___x_2238_);
v___x_2240_ = l_Lean_hasConst___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold_spec__0___redArg(v___x_2238_, v___x_2239_, v___y_2224_);
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2383_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2383_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v_nargs_2245_; lean_object* v___x_2246_; lean_object* v_dummy_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; uint8_t v___x_2366_; 
v_nargs_2245_ = l_Lean_Expr_getAppNumArgs(v_fst_2230_);
v___x_2246_ = l_Lean_Expr_constLevels_x21(v___x_2235_);
lean_dec_ref(v___x_2235_);
v_dummy_2247_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go___redArg___closed__0);
lean_inc(v_nargs_2245_);
v___x_2248_ = lean_mk_array(v_nargs_2245_, v_dummy_2247_);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_sub(v_nargs_2245_, v___x_2249_);
lean_dec(v_nargs_2245_);
v___x_2251_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_fst_2230_, v___x_2248_, v___x_2250_);
v___x_2366_ = lean_unbox(v_a_2241_);
lean_dec(v_a_2241_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v___x_2251_);
lean_dec(v___x_2246_);
lean_del_object(v___x_2243_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_cls_2220_);
v___x_2367_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__12);
v___x_2368_ = l_Lean_MessageData_ofName(v___x_2238_);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__14);
v___x_2371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2369_);
lean_ctor_set(v___x_2371_, 1, v___x_2370_);
v___x_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_mvarId_2218_);
v___x_2373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2373_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2374_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2374_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2374_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
else
{
v___y_2293_ = v___y_2221_;
v___y_2294_ = v___y_2222_;
v___y_2295_ = v___y_2223_;
v___y_2296_ = v___y_2224_;
goto v___jp_2292_;
}
v___jp_2252_:
{
lean_object* v___x_2261_; 
lean_inc(v___y_2260_);
lean_inc_ref(v___y_2259_);
lean_inc(v___y_2258_);
lean_inc_ref(v___y_2257_);
lean_inc_ref(v___y_2254_);
v___x_2261_ = lean_infer_type(v___y_2254_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__2));
v___x_2264_ = l_Lean_MVarId_define(v_mvarId_2218_, v___x_2263_, v_a_2262_, v___y_2254_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref(v___x_2264_);
v___x_2266_ = l_Lean_Meta_intro1Core(v_a_2265_, v___y_2253_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v_fst_2268_; lean_object* v_snd_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___f_2274_; lean_object* v___x_2275_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2266_);
v_fst_2268_ = lean_ctor_get(v_a_2267_, 0);
lean_inc(v_fst_2268_);
v_snd_2269_ = lean_ctor_get(v_a_2267_, 1);
lean_inc_n(v_snd_2269_, 2);
lean_dec(v_a_2267_);
v___x_2270_ = l_Lean_Expr_appFn_x21(v___y_2255_);
lean_dec_ref(v___y_2255_);
v___x_2271_ = l_Lean_mkFVar(v_fst_2268_);
v___x_2272_ = l_Lean_Expr_app___override(v___x_2270_, v___x_2271_);
v___x_2273_ = l_Lean_mkAppN(v___y_2256_, v___x_2251_);
lean_dec_ref(v___x_2251_);
v___f_2274_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2274_, 0, v_snd_2231_);
lean_closure_set(v___f_2274_, 1, v___x_2273_);
lean_closure_set(v___f_2274_, 2, v___x_2272_);
lean_closure_set(v___f_2274_, 3, v_snd_2269_);
v___x_2275_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_snd_2269_, v___f_2274_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
return v___x_2275_;
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___x_2251_);
lean_dec(v_snd_2231_);
v_a_2276_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2266_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2266_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___x_2251_);
lean_dec(v_snd_2231_);
return v___x_2264_;
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v___x_2251_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2218_);
v_a_2284_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2261_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2261_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
v___jp_2292_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; 
lean_inc(v___x_2238_);
v___x_2297_ = l_Lean_mkConst(v___x_2238_, v___x_2246_);
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc_ref(v___x_2297_);
v___x_2298_ = lean_infer_type(v___x_2297_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2300_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2298_);
v___x_2300_ = l_Lean_Meta_instantiateForall(v_a_2299_, v___x_2251_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2300_);
v___x_2302_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS___closed__1));
v___x_2303_ = lean_unsigned_to_nat(3u);
v___x_2304_ = l_Lean_Expr_isAppOfArity(v_a_2301_, v___x_2302_, v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
lean_dec(v_a_2301_);
lean_dec_ref(v___x_2297_);
lean_dec_ref(v___x_2251_);
lean_dec(v_snd_2231_);
lean_dec(v_cls_2220_);
v___x_2305_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__4);
v___x_2306_ = l_Lean_MessageData_ofName(v___x_2238_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 7);
lean_ctor_set(v___x_2233_, 1, v___x_2306_);
lean_ctor_set(v___x_2233_, 0, v___x_2305_);
v___x_2308_ = v___x_2233_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2309_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__6);
v___x_2310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2308_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set_tag(v___x_2243_, 1);
lean_ctor_set(v___x_2243_, 0, v_mvarId_2218_);
v___x_2312_ = v___x_2243_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_mvarId_2218_);
v___x_2312_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2310_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__0___redArg(v___x_2313_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v___x_2314_;
}
}
}
else
{
lean_object* v_options_2317_; lean_object* v_inheritedTraceOptions_2318_; uint8_t v_hasTrace_2319_; lean_object* v___x_2320_; lean_object* v_nargs_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_del_object(v___x_2243_);
lean_dec(v___x_2238_);
v_options_2317_ = lean_ctor_get(v___y_2295_, 2);
v_inheritedTraceOptions_2318_ = lean_ctor_get(v___y_2295_, 13);
v_hasTrace_2319_ = lean_ctor_get_uint8(v_options_2317_, sizeof(void*)*1);
v___x_2320_ = l_Lean_Expr_appArg_x21(v_a_2301_);
lean_dec(v_a_2301_);
v_nargs_2321_ = l_Lean_Expr_getAppNumArgs(v___x_2320_);
lean_inc(v_nargs_2321_);
v___x_2322_ = lean_mk_array(v_nargs_2321_, v_dummy_2247_);
v___x_2323_ = lean_nat_sub(v_nargs_2321_, v___x_2249_);
lean_dec(v_nargs_2321_);
lean_inc_ref(v___x_2320_);
v___x_2324_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___x_2320_, v___x_2322_, v___x_2323_);
v___x_2325_ = lean_array_get_size(v___x_2324_);
v___x_2326_ = lean_nat_sub(v___x_2325_, v___x_2249_);
v___x_2327_ = lean_array_get(v___x_2219_, v___x_2324_, v___x_2326_);
lean_dec(v___x_2326_);
lean_dec_ref(v___x_2324_);
if (v_hasTrace_2319_ == 0)
{
lean_del_object(v___x_2233_);
lean_dec(v_cls_2220_);
v___y_2253_ = v___x_2304_;
v___y_2254_ = v___x_2327_;
v___y_2255_ = v___x_2320_;
v___y_2256_ = v___x_2297_;
v___y_2257_ = v___y_2293_;
v___y_2258_ = v___y_2294_;
v___y_2259_ = v___y_2295_;
v___y_2260_ = v___y_2296_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2328_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
lean_inc(v_cls_2220_);
v___x_2329_ = l_Lean_Name_append(v___x_2328_, v_cls_2220_);
v___x_2330_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2318_, v_options_2317_, v___x_2329_);
lean_dec(v___x_2329_);
if (v___x_2330_ == 0)
{
lean_del_object(v___x_2233_);
lean_dec(v_cls_2220_);
v___y_2253_ = v___x_2304_;
v___y_2254_ = v___x_2327_;
v___y_2255_ = v___x_2320_;
v___y_2256_ = v___x_2297_;
v___y_2257_ = v___y_2293_;
v___y_2258_ = v___y_2294_;
v___y_2259_ = v___y_2295_;
v___y_2260_ = v___y_2296_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2335_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__8);
v___x_2332_ = lean_unsigned_to_nat(30u);
lean_inc(v___x_2327_);
v___x_2333_ = l_Lean_inlineExpr(v___x_2327_, v___x_2332_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set_tag(v___x_2233_, 7);
lean_ctor_set(v___x_2233_, 1, v___x_2333_);
lean_ctor_set(v___x_2233_, 0, v___x_2331_);
v___x_2335_ = v___x_2233_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2331_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2336_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___closed__10);
v___x_2337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
lean_inc_ref(v___x_2320_);
v___x_2338_ = l_Lean_indentExpr(v___x_2320_);
v___x_2339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2337_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(v_cls_2220_, v___x_2339_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_dec_ref(v___x_2340_);
v___y_2253_ = v___x_2304_;
v___y_2254_ = v___x_2327_;
v___y_2255_ = v___x_2320_;
v___y_2256_ = v___x_2297_;
v___y_2257_ = v___y_2293_;
v___y_2258_ = v___y_2294_;
v___y_2259_ = v___y_2295_;
v___y_2260_ = v___y_2296_;
goto v___jp_2252_;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v___x_2327_);
lean_dec_ref(v___x_2320_);
lean_dec_ref(v___x_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v___x_2251_);
lean_dec(v_snd_2231_);
lean_dec(v_mvarId_2218_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
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
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
lean_dec_ref(v___x_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v___x_2251_);
lean_del_object(v___x_2243_);
lean_dec(v___x_2238_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_cls_2220_);
lean_dec(v_mvarId_2218_);
v_a_2350_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2300_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2300_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v___x_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec_ref(v___x_2251_);
lean_del_object(v___x_2243_);
lean_dec(v___x_2238_);
lean_del_object(v___x_2233_);
lean_dec(v_snd_2231_);
lean_dec(v_cls_2220_);
lean_dec(v_mvarId_2218_);
v_a_2358_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2298_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2298_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v_cls_2220_);
lean_dec(v_mvarId_2218_);
v_a_2385_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2228_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2228_);
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
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v_cls_2220_);
lean_dec(v_mvarId_2218_);
v_a_2393_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2226_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2226_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed(lean_object* v_mvarId_2401_, lean_object* v___x_2402_, lean_object* v_cls_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1(v_mvarId_2401_, v___x_2402_, v_cls_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec_ref(v___x_2402_);
return v_res_2409_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__0));
v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(lean_object* v_mvarId_2413_, lean_object* v_x_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2420_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___closed__1);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v_mvarId_2413_);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed(lean_object* v_mvarId_2424_, lean_object* v_x_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2(v_mvarId_2424_, v_x_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec_ref(v_x_2425_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(lean_object* v_declName_2432_, lean_object* v_mvarId_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_options_2439_; lean_object* v_inheritedTraceOptions_2440_; uint8_t v_hasTrace_2441_; lean_object* v___x_2442_; lean_object* v_cls_2443_; lean_object* v___f_2444_; 
v_options_2439_ = lean_ctor_get(v_a_2436_, 2);
v_inheritedTraceOptions_2440_ = lean_ctor_get(v_a_2436_, 13);
v_hasTrace_2441_ = lean_ctor_get_uint8(v_options_2439_, sizeof(void*)*1);
v___x_2442_ = l_Lean_instInhabitedExpr;
v_cls_2443_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
lean_inc(v_mvarId_2433_);
v___f_2444_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2444_, 0, v_mvarId_2433_);
lean_closure_set(v___f_2444_, 1, v___x_2442_);
lean_closure_set(v___f_2444_, 2, v_cls_2443_);
if (v_hasTrace_2441_ == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2433_, v___f_2444_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2445_);
v___x_2447_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2432_, v_a_2446_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2447_;
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_declName_2432_);
v_a_2448_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2445_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2445_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
else
{
lean_object* v___f_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v_a_2463_; lean_object* v___y_2476_; lean_object* v___y_2477_; lean_object* v_a_2478_; lean_object* v___y_2481_; lean_object* v___y_2482_; lean_object* v_a_2483_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v_a_2495_; 
lean_inc(v_mvarId_2433_);
v___f_2456_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___lam__2___boxed), 7, 1);
lean_closure_set(v___f_2456_, 0, v_mvarId_2433_);
v___x_2457_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__1));
v___x_2458_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__20);
v___x_2459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2440_, v_options_2439_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = l_Lean_trace_profiler;
v___x_2531_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2439_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; 
lean_dec_ref(v___f_2456_);
v___x_2532_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2433_, v___f_2444_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
v___x_2534_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2432_, v_a_2533_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2534_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_declName_2432_);
v_a_2535_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2532_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2532_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
goto v___jp_2497_;
}
}
else
{
goto v___jp_2497_;
}
v___jp_2460_:
{
lean_object* v___x_2464_; double v___x_2465_; double v___x_2466_; double v___x_2467_; double v___x_2468_; double v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2464_ = lean_io_mono_nanos_now();
v___x_2465_ = lean_float_of_nat(v___y_2461_);
v___x_2466_ = lean_float_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__21);
v___x_2467_ = lean_float_div(v___x_2465_, v___x_2466_);
v___x_2468_ = lean_float_of_nat(v___x_2464_);
v___x_2469_ = lean_float_div(v___x_2468_, v___x_2466_);
v___x_2470_ = lean_box_float(v___x_2467_);
v___x_2471_ = lean_box_float(v___x_2469_);
v___x_2472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_a_2463_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2443_, v_hasTrace_2441_, v___x_2457_, v_options_2439_, v___x_2459_, v___y_2462_, v___f_2456_, v___x_2473_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2474_;
}
v___jp_2475_:
{
lean_object* v___x_2479_; 
v___x_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2479_, 0, v_a_2478_);
v___y_2461_ = v___y_2476_;
v___y_2462_ = v___y_2477_;
v_a_2463_ = v___x_2479_;
goto v___jp_2460_;
}
v___jp_2480_:
{
lean_object* v___x_2484_; double v___x_2485_; double v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2484_ = lean_io_get_num_heartbeats();
v___x_2485_ = lean_float_of_nat(v___y_2482_);
v___x_2486_ = lean_float_of_nat(v___x_2484_);
v___x_2487_ = lean_box_float(v___x_2485_);
v___x_2488_ = lean_box_float(v___x_2486_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2487_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v_a_2483_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5(v_cls_2443_, v_hasTrace_2441_, v___x_2457_, v_options_2439_, v___x_2459_, v___y_2481_, v___f_2456_, v___x_2490_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
return v___x_2491_;
}
v___jp_2492_:
{
lean_object* v___x_2496_; 
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v_a_2495_);
v___y_2481_ = v___y_2493_;
v___y_2482_ = v___y_2494_;
v_a_2483_ = v___x_2496_;
goto v___jp_2480_;
}
v___jp_2497_:
{
lean_object* v___x_2498_; lean_object* v_a_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2498_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2437_);
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2501_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2439_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_io_mono_nanos_now();
v___x_2503_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2433_, v___f_2444_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref(v___x_2503_);
v___x_2505_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2432_, v_a_2504_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set_tag(v___x_2508_, 1);
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
v___y_2461_ = v___x_2502_;
v___y_2462_ = v_a_2499_;
v_a_2463_ = v___x_2511_;
goto v___jp_2460_;
}
}
}
else
{
lean_object* v_a_2514_; 
v_a_2514_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2514_);
lean_dec_ref(v___x_2505_);
v___y_2476_ = v___x_2502_;
v___y_2477_ = v_a_2499_;
v_a_2478_ = v_a_2514_;
goto v___jp_2475_;
}
}
else
{
lean_object* v_a_2515_; 
lean_dec(v_declName_2432_);
v_a_2515_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v___x_2503_);
v___y_2476_ = v___x_2502_;
v___y_2477_ = v_a_2499_;
v_a_2478_ = v_a_2515_;
goto v___jp_2475_;
}
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_io_get_num_heartbeats();
v___x_2517_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_deltaRHS_x3f_spec__0___redArg(v_mvarId_2433_, v___f_2444_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2519_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2518_);
lean_dec_ref(v___x_2517_);
v___x_2519_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(v_declName_2432_, v_a_2518_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 1);
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
v___y_2481_ = v_a_2499_;
v___y_2482_ = v___x_2516_;
v_a_2483_ = v___x_2525_;
goto v___jp_2480_;
}
}
}
else
{
lean_object* v_a_2528_; 
v_a_2528_ = lean_ctor_get(v___x_2519_, 0);
lean_inc(v_a_2528_);
lean_dec_ref(v___x_2519_);
v___y_2493_ = v_a_2499_;
v___y_2494_ = v___x_2516_;
v_a_2495_ = v_a_2528_;
goto v___jp_2492_;
}
}
else
{
lean_object* v_a_2529_; 
lean_dec(v_declName_2432_);
v_a_2529_ = lean_ctor_get(v___x_2517_, 0);
lean_inc(v_a_2529_);
lean_dec_ref(v___x_2517_);
v___y_2493_ = v_a_2499_;
v___y_2494_ = v___x_2516_;
v_a_2495_ = v_a_2529_;
goto v___jp_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold___boxed(lean_object* v_declName_2543_, lean_object* v_mvarId_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2543_, v_mvarId_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(lean_object* v_e_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v___x_2554_; 
v___x_2554_ = l_Lean_Expr_hasMVar(v_e_2551_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v_e_2551_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; lean_object* v_mctx_2557_; lean_object* v___x_2558_; lean_object* v_fst_2559_; lean_object* v_snd_2560_; lean_object* v___x_2561_; lean_object* v_cache_2562_; lean_object* v_zetaDeltaFVarIds_2563_; lean_object* v_postponed_2564_; lean_object* v_diag_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2574_; 
v___x_2556_ = lean_st_ref_get(v___y_2552_);
v_mctx_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc_ref(v_mctx_2557_);
lean_dec(v___x_2556_);
v___x_2558_ = l_Lean_instantiateMVarsCore(v_mctx_2557_, v_e_2551_);
v_fst_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_fst_2559_);
v_snd_2560_ = lean_ctor_get(v___x_2558_, 1);
lean_inc(v_snd_2560_);
lean_dec_ref(v___x_2558_);
v___x_2561_ = lean_st_ref_take(v___y_2552_);
v_cache_2562_ = lean_ctor_get(v___x_2561_, 1);
v_zetaDeltaFVarIds_2563_ = lean_ctor_get(v___x_2561_, 2);
v_postponed_2564_ = lean_ctor_get(v___x_2561_, 3);
v_diag_2565_ = lean_ctor_get(v___x_2561_, 4);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2574_ == 0)
{
lean_object* v_unused_2575_; 
v_unused_2575_ = lean_ctor_get(v___x_2561_, 0);
lean_dec(v_unused_2575_);
v___x_2567_ = v___x_2561_;
v_isShared_2568_ = v_isSharedCheck_2574_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_diag_2565_);
lean_inc(v_postponed_2564_);
lean_inc(v_zetaDeltaFVarIds_2563_);
lean_inc(v_cache_2562_);
lean_dec(v___x_2561_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2574_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v_snd_2560_);
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_snd_2560_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_cache_2562_);
lean_ctor_set(v_reuseFailAlloc_2573_, 2, v_zetaDeltaFVarIds_2563_);
lean_ctor_set(v_reuseFailAlloc_2573_, 3, v_postponed_2564_);
lean_ctor_set(v_reuseFailAlloc_2573_, 4, v_diag_2565_);
v___x_2570_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = lean_st_ref_set(v___y_2552_, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_fst_2559_);
return v___x_2572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg___boxed(lean_object* v_e_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2576_, v___y_2577_);
lean_dec(v___y_2577_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(lean_object* v_e_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_e_2580_, v___y_2582_);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___boxed(lean_object* v_e_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0(v_e_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(lean_object* v_k_2594_, uint8_t v_allowLevelAssignments_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2595_, v_k_2594_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2609_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2607_; 
if (v_isShared_2605_ == 0)
{
v___x_2607_ = v___x_2604_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_a_2602_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2601_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2601_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg___boxed(lean_object* v_k_2618_, lean_object* v_allowLevelAssignments_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2625_; lean_object* v_res_2626_; 
v_allowLevelAssignments_boxed_2625_ = lean_unbox(v_allowLevelAssignments_2619_);
v_res_2626_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2618_, v_allowLevelAssignments_boxed_2625_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(lean_object* v_00_u03b1_2627_, lean_object* v_k_2628_, uint8_t v_allowLevelAssignments_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___redArg(v_k_2628_, v_allowLevelAssignments_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed(lean_object* v_00_u03b1_2636_, lean_object* v_k_2637_, lean_object* v_allowLevelAssignments_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2644_; lean_object* v_res_2645_; 
v_allowLevelAssignments_boxed_2644_ = lean_unbox(v_allowLevelAssignments_2638_);
v_res_2645_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1(v_00_u03b1_2636_, v_k_2637_, v_allowLevelAssignments_boxed_2644_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* v___x_2646_, lean_object* v_e_2647_){
_start:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = l_Lean_indentD(v_e_2647_);
v___x_2649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2646_);
lean_ctor_set(v___x_2649_, 1, v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(lean_object* v_type_2650_, lean_object* v___x_2651_, lean_object* v_declName_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_type_2650_, v___x_2651_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref(v___x_2658_);
v___x_2660_ = l_Lean_Expr_mvarId_x21(v_a_2659_);
v___x_2661_ = l_Lean_MVarId_intros(v___x_2660_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v_snd_2663_; lean_object* v___x_2664_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref(v___x_2661_);
v_snd_2663_ = lean_ctor_get(v_a_2662_, 1);
lean_inc_n(v_snd_2663_, 2);
lean_dec(v_a_2662_);
v___x_2664_ = l_Lean_Elab_Eqns_tryURefl(v_snd_2663_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; uint8_t v___x_2666_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = lean_unbox(v_a_2665_);
lean_dec(v_a_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
v___x_2667_ = l_Lean_Elab_Eqns_deltaLHS(v_snd_2663_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2669_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_goUnfold(v_declName_2652_, v_a_2668_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2670_; 
lean_dec_ref(v___x_2669_);
v___x_2670_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2659_, v___y_2654_);
return v___x_2670_;
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v_a_2659_);
v_a_2671_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2669_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2669_);
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
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_a_2659_);
lean_dec(v_declName_2652_);
v_a_2679_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2667_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2667_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_object* v___x_2687_; 
lean_dec(v_snd_2663_);
lean_dec(v_declName_2652_);
v___x_2687_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__0___redArg(v_a_2659_, v___y_2654_);
return v___x_2687_;
}
}
else
{
lean_object* v_a_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_snd_2663_);
lean_dec(v_a_2659_);
lean_dec(v_declName_2652_);
v_a_2688_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2690_ = v___x_2664_;
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_a_2688_);
lean_dec(v___x_2664_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2695_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2693_; 
if (v_isShared_2691_ == 0)
{
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
return v___x_2693_;
}
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_a_2659_);
lean_dec(v_declName_2652_);
v_a_2696_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2661_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2661_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_dec(v_declName_2652_);
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed(lean_object* v_type_2704_, lean_object* v___x_2705_, lean_object* v_declName_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1(v_type_2704_, v___x_2705_, v_declName_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2712_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__0));
v___x_2715_ = l_Lean_stringToMessageData(v___x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(lean_object* v_type_2716_, lean_object* v_x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2723_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___closed__1);
v___x_2724_ = l_Lean_indentExpr(v_type_2716_);
v___x_2725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2___boxed(lean_object* v_type_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__2(v_type_2727_, v_x_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec_ref(v_x_2728_);
return v_res_2734_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(lean_object* v_e_2735_){
_start:
{
if (lean_obj_tag(v_e_2735_) == 0)
{
uint8_t v___x_2736_; 
v___x_2736_ = 2;
return v___x_2736_;
}
else
{
uint8_t v___x_2737_; 
v___x_2737_ = 0;
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2___boxed(lean_object* v_e_2738_){
_start:
{
uint8_t v_res_2739_; lean_object* v_r_2740_; 
v_res_2739_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_e_2738_);
lean_dec_ref(v_e_2738_);
v_r_2740_ = lean_box(v_res_2739_);
return v_r_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(lean_object* v_cls_2741_, uint8_t v_collapsed_2742_, lean_object* v_tag_2743_, lean_object* v_opts_2744_, uint8_t v_clsEnabled_2745_, lean_object* v_oldTraces_2746_, lean_object* v_msg_2747_, lean_object* v_resStartStop_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_fst_2754_; lean_object* v_snd_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2854_; 
v_fst_2754_ = lean_ctor_get(v_resStartStop_2748_, 0);
v_snd_2755_ = lean_ctor_get(v_resStartStop_2748_, 1);
v_isSharedCheck_2854_ = !lean_is_exclusive(v_resStartStop_2748_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2757_ = v_resStartStop_2748_;
v_isShared_2758_ = v_isSharedCheck_2854_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_snd_2755_);
lean_inc(v_fst_2754_);
lean_dec(v_resStartStop_2748_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2854_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v_data_2762_; lean_object* v_fst_2773_; lean_object* v_snd_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2853_; 
v_fst_2773_ = lean_ctor_get(v_snd_2755_, 0);
v_snd_2774_ = lean_ctor_get(v_snd_2755_, 1);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_snd_2755_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2776_ = v_snd_2755_;
v_isShared_2777_ = v_isSharedCheck_2853_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_snd_2774_);
lean_inc(v_fst_2773_);
lean_dec(v_snd_2755_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2853_;
goto v_resetjp_2775_;
}
v___jp_2759_:
{
lean_object* v___x_2763_; 
lean_inc(v___y_2761_);
v___x_2763_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__6(v_oldTraces_2746_, v_data_2762_, v___y_2761_, v___y_2760_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v___x_2764_; 
lean_dec_ref(v___x_2763_);
v___x_2764_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_2754_);
return v___x_2764_;
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
lean_dec(v_fst_2754_);
v_a_2765_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2763_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2763_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; uint8_t v___x_2779_; lean_object* v___y_2781_; lean_object* v_a_2782_; uint8_t v___y_2806_; double v___y_2838_; 
v___x_2778_ = l_Lean_trace_profiler;
v___x_2779_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2744_, v___x_2778_);
if (v___x_2779_ == 0)
{
v___y_2806_ = v___x_2779_;
goto v___jp_2805_;
}
else
{
lean_object* v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2844_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_opts_2744_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; lean_object* v___x_2846_; double v___x_2847_; double v___x_2848_; double v___x_2849_; 
v___x_2845_ = l_Lean_trace_profiler_threshold;
v___x_2846_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2744_, v___x_2845_);
v___x_2847_ = lean_float_of_nat(v___x_2846_);
v___x_2848_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__4);
v___x_2849_ = lean_float_div(v___x_2847_, v___x_2848_);
v___y_2838_ = v___x_2849_;
goto v___jp_2837_;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; double v___x_2852_; 
v___x_2850_ = l_Lean_trace_profiler_threshold;
v___x_2851_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v_opts_2744_, v___x_2850_);
v___x_2852_ = lean_float_of_nat(v___x_2851_);
v___y_2838_ = v___x_2852_;
goto v___jp_2837_;
}
}
v___jp_2780_:
{
uint8_t v_result_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v_result_2783_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2_spec__2(v_fst_2754_);
v___x_2784_ = l_Lean_TraceResult_toEmoji(v_result_2783_);
v___x_2785_ = l_Lean_stringToMessageData(v___x_2784_);
v___x_2786_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__1);
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 7);
lean_ctor_set(v___x_2776_, 1, v___x_2786_);
lean_ctor_set(v___x_2776_, 0, v___x_2785_);
v___x_2788_ = v___x_2776_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2785_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v_m_2790_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 7);
lean_ctor_set(v___x_2757_, 1, v_a_2782_);
lean_ctor_set(v___x_2757_, 0, v___x_2788_);
v_m_2790_ = v___x_2757_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_a_2782_);
v_m_2790_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; double v___x_2793_; lean_object* v_data_2794_; 
v___x_2791_ = lean_box(v_result_2783_);
v___x_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
v___x_2793_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0___closed__0);
lean_inc_ref(v_tag_2743_);
lean_inc_ref(v___x_2792_);
lean_inc(v_cls_2741_);
v_data_2794_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2794_, 0, v_cls_2741_);
lean_ctor_set(v_data_2794_, 1, v___x_2792_);
lean_ctor_set(v_data_2794_, 2, v_tag_2743_);
lean_ctor_set_float(v_data_2794_, sizeof(void*)*3, v___x_2793_);
lean_ctor_set_float(v_data_2794_, sizeof(void*)*3 + 8, v___x_2793_);
lean_ctor_set_uint8(v_data_2794_, sizeof(void*)*3 + 16, v_collapsed_2742_);
if (v___x_2779_ == 0)
{
lean_dec_ref(v___x_2792_);
lean_dec(v_snd_2774_);
lean_dec(v_fst_2773_);
lean_dec_ref(v_tag_2743_);
lean_dec(v_cls_2741_);
v___y_2760_ = v_m_2790_;
v___y_2761_ = v___y_2781_;
v_data_2762_ = v_data_2794_;
goto v___jp_2759_;
}
else
{
lean_object* v_data_2795_; double v___x_2796_; double v___x_2797_; 
lean_dec_ref(v_data_2794_);
v_data_2795_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2795_, 0, v_cls_2741_);
lean_ctor_set(v_data_2795_, 1, v___x_2792_);
lean_ctor_set(v_data_2795_, 2, v_tag_2743_);
v___x_2796_ = lean_unbox_float(v_fst_2773_);
lean_dec(v_fst_2773_);
lean_ctor_set_float(v_data_2795_, sizeof(void*)*3, v___x_2796_);
v___x_2797_ = lean_unbox_float(v_snd_2774_);
lean_dec(v_snd_2774_);
lean_ctor_set_float(v_data_2795_, sizeof(void*)*3 + 8, v___x_2797_);
lean_ctor_set_uint8(v_data_2795_, sizeof(void*)*3 + 16, v_collapsed_2742_);
v___y_2760_ = v_m_2790_;
v___y_2761_ = v___y_2781_;
v_data_2762_ = v_data_2795_;
goto v___jp_2759_;
}
}
}
}
v___jp_2800_:
{
lean_object* v_ref_2801_; lean_object* v___x_2802_; 
v_ref_2801_ = lean_ctor_get(v___y_2751_, 5);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v_fst_2754_);
v___x_2802_ = lean_apply_6(v_msg_2747_, v_fst_2754_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, lean_box(0));
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref(v___x_2802_);
v___y_2781_ = v_ref_2801_;
v_a_2782_ = v_a_2803_;
goto v___jp_2780_;
}
else
{
lean_object* v___x_2804_; 
lean_dec_ref(v___x_2802_);
v___x_2804_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5___closed__3);
v___y_2781_ = v_ref_2801_;
v_a_2782_ = v___x_2804_;
goto v___jp_2780_;
}
}
v___jp_2805_:
{
if (v_clsEnabled_2745_ == 0)
{
if (v___y_2806_ == 0)
{
lean_object* v___x_2807_; lean_object* v_traceState_2808_; lean_object* v_env_2809_; lean_object* v_nextMacroScope_2810_; lean_object* v_ngen_2811_; lean_object* v_auxDeclNGen_2812_; lean_object* v_cache_2813_; lean_object* v_messages_2814_; lean_object* v_infoState_2815_; lean_object* v_snapshotTasks_2816_; lean_object* v_newDecls_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2836_; 
lean_del_object(v___x_2776_);
lean_dec(v_snd_2774_);
lean_dec(v_fst_2773_);
lean_del_object(v___x_2757_);
lean_dec_ref(v_msg_2747_);
lean_dec_ref(v_tag_2743_);
lean_dec(v_cls_2741_);
v___x_2807_ = lean_st_ref_take(v___y_2752_);
v_traceState_2808_ = lean_ctor_get(v___x_2807_, 4);
v_env_2809_ = lean_ctor_get(v___x_2807_, 0);
v_nextMacroScope_2810_ = lean_ctor_get(v___x_2807_, 1);
v_ngen_2811_ = lean_ctor_get(v___x_2807_, 2);
v_auxDeclNGen_2812_ = lean_ctor_get(v___x_2807_, 3);
v_cache_2813_ = lean_ctor_get(v___x_2807_, 5);
v_messages_2814_ = lean_ctor_get(v___x_2807_, 6);
v_infoState_2815_ = lean_ctor_get(v___x_2807_, 7);
v_snapshotTasks_2816_ = lean_ctor_get(v___x_2807_, 8);
v_newDecls_2817_ = lean_ctor_get(v___x_2807_, 9);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2819_ = v___x_2807_;
v_isShared_2820_ = v_isSharedCheck_2836_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_newDecls_2817_);
lean_inc(v_snapshotTasks_2816_);
lean_inc(v_infoState_2815_);
lean_inc(v_messages_2814_);
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
v___x_2826_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2746_, v_traces_2822_);
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
lean_ctor_set(v_reuseFailAlloc_2833_, 6, v_messages_2814_);
lean_ctor_set(v_reuseFailAlloc_2833_, 7, v_infoState_2815_);
lean_ctor_set(v_reuseFailAlloc_2833_, 8, v_snapshotTasks_2816_);
lean_ctor_set(v_reuseFailAlloc_2833_, 9, v_newDecls_2817_);
v___x_2830_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_st_ref_set(v___y_2752_, v___x_2830_);
v___x_2832_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__7___redArg(v_fst_2754_);
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
v___x_2839_ = lean_unbox_float(v_snd_2774_);
v___x_2840_ = lean_unbox_float(v_fst_2773_);
v___x_2841_ = lean_float_sub(v___x_2839_, v___x_2840_);
v___x_2842_ = lean_float_decLt(v___y_2838_, v___x_2841_);
v___y_2806_ = v___x_2842_;
goto v___jp_2805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2___boxed(lean_object* v_cls_2855_, lean_object* v_collapsed_2856_, lean_object* v_tag_2857_, lean_object* v_opts_2858_, lean_object* v_clsEnabled_2859_, lean_object* v_oldTraces_2860_, lean_object* v_msg_2861_, lean_object* v_resStartStop_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
uint8_t v_collapsed_boxed_2868_; uint8_t v_clsEnabled_boxed_2869_; lean_object* v_res_2870_; 
v_collapsed_boxed_2868_ = lean_unbox(v_collapsed_2856_);
v_clsEnabled_boxed_2869_ = lean_unbox(v_clsEnabled_2859_);
v_res_2870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v_cls_2855_, v_collapsed_boxed_2868_, v_tag_2857_, v_opts_2858_, v_clsEnabled_boxed_2869_, v_oldTraces_2860_, v_msg_2861_, v_resStartStop_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec_ref(v___y_2865_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v_opts_2858_);
return v_res_2870_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__1(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__0));
v___x_2873_ = l_Lean_stringToMessageData(v___x_2872_);
return v___x_2873_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__3(void){
_start:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___closed__2));
v___x_2876_ = l_Lean_stringToMessageData(v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* v_declName_2877_, lean_object* v_type_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_options_2884_; lean_object* v_inheritedTraceOptions_2885_; uint8_t v_hasTrace_2886_; uint8_t v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_options_2884_ = lean_ctor_get(v_a_2881_, 2);
v_inheritedTraceOptions_2885_ = lean_ctor_get(v_a_2881_, 13);
v_hasTrace_2886_ = lean_ctor_get_uint8(v_options_2884_, sizeof(void*)*1);
v___x_2887_ = 0;
lean_inc(v_declName_2877_);
v___x_2888_ = l_Lean_MessageData_ofConstName(v_declName_2877_, v___x_2887_);
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
lean_inc_ref(v_type_2878_);
v___f_2895_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__1___boxed), 8, 3);
lean_closure_set(v___f_2895_, 0, v_type_2878_);
lean_closure_set(v___f_2895_, 1, v___x_2894_);
lean_closure_set(v___f_2895_, 2, v_declName_2877_);
v___x_2896_ = lean_box(v___x_2887_);
v___x_2897_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__1___boxed), 8, 3);
lean_closure_set(v___x_2897_, 0, lean_box(0));
lean_closure_set(v___x_2897_, 1, v___f_2895_);
lean_closure_set(v___x_2897_, 2, v___x_2896_);
if (v_hasTrace_2886_ == 0)
{
lean_object* v___x_2898_; 
lean_dec_ref(v_type_2878_);
v___x_2898_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
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
lean_closure_set(v___f_2915_, 0, v_type_2878_);
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
v___x_2990_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
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
v___x_2934_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2916_, v_hasTrace_2886_, v___x_2917_, v_options_2884_, v___x_2919_, v___y_2922_, v___f_2915_, v___x_2933_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
return v___x_2934_;
}
v___jp_2935_:
{
lean_object* v___x_2939_; double v___x_2940_; double v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2939_ = lean_io_get_num_heartbeats();
v___x_2940_ = lean_float_of_nat(v___y_2936_);
v___x_2941_ = lean_float_of_nat(v___x_2939_);
v___x_2942_ = lean_box_float(v___x_2940_);
v___x_2943_ = lean_box_float(v___x_2941_);
v___x_2944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2942_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v_a_2938_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_spec__2(v___x_2916_, v_hasTrace_2886_, v___x_2917_, v_options_2884_, v___x_2919_, v___y_2937_, v___f_2915_, v___x_2945_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
return v___x_2946_;
}
v___jp_2947_:
{
lean_object* v___x_2948_; lean_object* v_a_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2948_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__3___redArg(v_a_2882_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v___x_2950_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2951_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v_options_2884_, v___x_2950_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_io_mono_nanos_now();
v___x_2953_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
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
v___x_2971_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2897_, v___f_2893_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
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
v___y_2936_ = v___x_2970_;
v___y_2937_ = v_a_2949_;
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
v___y_2936_ = v___x_2970_;
v___y_2937_ = v_a_2949_;
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(lean_object* v_env_3015_, lean_object* v_n_3016_, lean_object* v_x_3017_){
_start:
{
uint8_t v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; 
v___x_3018_ = 1;
v___x_3019_ = l_Lean_Environment_setExporting(v_env_3015_, v___x_3018_);
v___x_3020_ = 0;
v___x_3021_ = l_Lean_Environment_find_x3f(v___x_3019_, v_n_3016_, v___x_3020_);
if (lean_obj_tag(v___x_3021_) == 0)
{
return v___x_3020_;
}
else
{
lean_object* v_val_3022_; uint8_t v___x_3023_; 
v_val_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_val_3022_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = l_Lean_ConstantInfo_hasValue(v_val_3022_, v___x_3020_);
lean_dec(v_val_3022_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed(lean_object* v_env_3024_, lean_object* v_n_3025_, lean_object* v_x_3026_){
_start:
{
uint8_t v_res_3027_; lean_object* v_r_3028_; 
v_res_3027_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(v_env_3024_, v_n_3025_, v_x_3026_);
lean_dec_ref(v_x_3026_);
v_r_3028_ = lean_box(v_res_3027_);
return v_r_3028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_3029_, lean_object* v_x_3030_){
_start:
{
if (lean_obj_tag(v_x_3030_) == 0)
{
lean_object* v_k_3031_; lean_object* v_v_3032_; lean_object* v_l_3033_; lean_object* v_r_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_k_3031_ = lean_ctor_get(v_x_3030_, 1);
v_v_3032_ = lean_ctor_get(v_x_3030_, 2);
v_l_3033_ = lean_ctor_get(v_x_3030_, 3);
v_r_3034_ = lean_ctor_get(v_x_3030_, 4);
v___x_3035_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_3029_, v_l_3033_);
lean_inc(v_v_3032_);
lean_inc(v_k_3031_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v_k_3031_);
lean_ctor_set(v___x_3036_, 1, v_v_3032_);
v___x_3037_ = lean_array_push(v___x_3035_, v___x_3036_);
v_init_3029_ = v___x_3037_;
v_x_3030_ = v_r_3034_;
goto _start;
}
else
{
return v_init_3029_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_3039_, lean_object* v_x_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_3039_, v_x_3040_);
lean_dec(v_x_3040_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(lean_object* v_env_3044_, lean_object* v_s_3045_){
_start:
{
lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v_all_3048_; lean_object* v___x_3049_; lean_object* v_exported_3050_; lean_object* v___x_3051_; 
v___f_3046_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed), 3, 1);
lean_closure_set(v___f_3046_, 0, v_env_3044_);
v___x_3047_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___lam__1___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v_all_3048_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_3047_, v_s_3045_);
v___x_3049_ = l_Std_DTreeMap_Internal_Impl_filter___at___00Lean_NameMap_filter_spec__0___redArg(v___f_3046_, v_s_3045_);
v_exported_3050_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v___x_3047_, v___x_3049_);
lean_dec(v___x_3049_);
lean_inc_ref(v_exported_3050_);
v___x_3051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3051_, 0, v_exported_3050_);
lean_ctor_set(v___x_3051_, 1, v_exported_3050_);
lean_ctor_set(v___x_3051_, 2, v_all_3048_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___f_3064_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v___x_3066_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_));
v___x_3067_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_3065_, v___x_3066_, v___f_3064_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2____boxed(lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2_();
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0(lean_object* v_init_3070_, lean_object* v_t_3071_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0_spec__0(v_init_3070_, v_t_3071_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_3073_, lean_object* v_t_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_1195399529____hygCtx___hyg_2__spec__0(v_init_3073_, v_t_3074_);
lean_dec(v_t_3074_);
return v_res_3075_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0(void){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__0, &l_Lean_Elab_Structural_registerEqnsInfo___closed__0_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__0);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3079_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* v_preDef_3081_, lean_object* v_declNames_3082_, lean_object* v_recArgPos_3083_, lean_object* v_fixedParamPerms_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v_levelParams_3088_; lean_object* v_declName_3089_; lean_object* v_type_3090_; lean_object* v_value_3091_; lean_object* v___x_3092_; 
v_levelParams_3088_ = lean_ctor_get(v_preDef_3081_, 1);
lean_inc(v_levelParams_3088_);
v_declName_3089_ = lean_ctor_get(v_preDef_3081_, 3);
lean_inc_n(v_declName_3089_, 2);
v_type_3090_ = lean_ctor_get(v_preDef_3081_, 6);
lean_inc_ref(v_type_3090_);
v_value_3091_ = lean_ctor_get(v_preDef_3081_, 7);
lean_inc_ref(v_value_3091_);
lean_dec_ref(v_preDef_3081_);
v___x_3092_ = l_Lean_Meta_ensureEqnReservedNamesAvailable(v_declName_3089_, v_a_3085_, v_a_3086_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3123_; 
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v___x_3092_, 0);
lean_dec(v_unused_3124_);
v___x_3094_ = v___x_3092_;
v_isShared_3095_ = v_isSharedCheck_3123_;
goto v_resetjp_3093_;
}
else
{
lean_dec(v___x_3092_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3123_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3096_; lean_object* v_env_3097_; lean_object* v_nextMacroScope_3098_; lean_object* v_ngen_3099_; lean_object* v_auxDeclNGen_3100_; lean_object* v_traceState_3101_; lean_object* v_messages_3102_; lean_object* v_infoState_3103_; lean_object* v_snapshotTasks_3104_; lean_object* v_newDecls_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3121_; 
v___x_3096_ = lean_st_ref_take(v_a_3086_);
v_env_3097_ = lean_ctor_get(v___x_3096_, 0);
v_nextMacroScope_3098_ = lean_ctor_get(v___x_3096_, 1);
v_ngen_3099_ = lean_ctor_get(v___x_3096_, 2);
v_auxDeclNGen_3100_ = lean_ctor_get(v___x_3096_, 3);
v_traceState_3101_ = lean_ctor_get(v___x_3096_, 4);
v_messages_3102_ = lean_ctor_get(v___x_3096_, 6);
v_infoState_3103_ = lean_ctor_get(v___x_3096_, 7);
v_snapshotTasks_3104_ = lean_ctor_get(v___x_3096_, 8);
v_newDecls_3105_ = lean_ctor_get(v___x_3096_, 9);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v___x_3096_, 5);
lean_dec(v_unused_3122_);
v___x_3107_ = v___x_3096_;
v_isShared_3108_ = v_isSharedCheck_3121_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_newDecls_3105_);
lean_inc(v_snapshotTasks_3104_);
lean_inc(v_infoState_3103_);
lean_inc(v_messages_3102_);
lean_inc(v_traceState_3101_);
lean_inc(v_auxDeclNGen_3100_);
lean_inc(v_ngen_3099_);
lean_inc(v_nextMacroScope_3098_);
lean_inc(v_env_3097_);
lean_dec(v___x_3096_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3121_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3109_ = l_Lean_Elab_Structural_eqnInfoExt;
lean_inc(v_declName_3089_);
v___x_3110_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3110_, 0, v_declName_3089_);
lean_ctor_set(v___x_3110_, 1, v_levelParams_3088_);
lean_ctor_set(v___x_3110_, 2, v_type_3090_);
lean_ctor_set(v___x_3110_, 3, v_value_3091_);
lean_ctor_set(v___x_3110_, 4, v_recArgPos_3083_);
lean_ctor_set(v___x_3110_, 5, v_declNames_3082_);
lean_ctor_set(v___x_3110_, 6, v_fixedParamPerms_3084_);
v___x_3111_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3109_, v_env_3097_, v_declName_3089_, v___x_3110_);
v___x_3112_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 5, v___x_3112_);
lean_ctor_set(v___x_3107_, 0, v___x_3111_);
v___x_3114_ = v___x_3107_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_nextMacroScope_3098_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_ngen_3099_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v_auxDeclNGen_3100_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v_traceState_3101_);
lean_ctor_set(v_reuseFailAlloc_3120_, 5, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3120_, 6, v_messages_3102_);
lean_ctor_set(v_reuseFailAlloc_3120_, 7, v_infoState_3103_);
lean_ctor_set(v_reuseFailAlloc_3120_, 8, v_snapshotTasks_3104_);
lean_ctor_set(v_reuseFailAlloc_3120_, 9, v_newDecls_3105_);
v___x_3114_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3115_ = lean_st_ref_set(v_a_3086_, v___x_3114_);
v___x_3116_ = lean_box(0);
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3116_);
v___x_3118_ = v___x_3094_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_3116_);
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
else
{
lean_dec_ref(v_value_3091_);
lean_dec_ref(v_type_3090_);
lean_dec(v_declName_3089_);
lean_dec(v_levelParams_3088_);
lean_dec_ref(v_fixedParamPerms_3084_);
lean_dec(v_recArgPos_3083_);
lean_dec_ref(v_declNames_3082_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* v_preDef_3125_, lean_object* v_declNames_3126_, lean_object* v_recArgPos_3127_, lean_object* v_fixedParamPerms_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Elab_Structural_registerEqnsInfo(v_preDef_3125_, v_declNames_3126_, v_recArgPos_3127_, v_fixedParamPerms_3128_, v_a_3129_, v_a_3130_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(lean_object* v_e_3133_, lean_object* v_k_3134_, uint8_t v_cleanupAnnotations_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_){
_start:
{
lean_object* v___f_3141_; uint8_t v___x_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___f_3141_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_findBRecOnLHS_go_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3141_, 0, v_k_3134_);
v___x_3142_ = 1;
v___x_3143_ = 0;
v___x_3144_ = lean_box(0);
v___x_3145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3133_, v___x_3142_, v___x_3143_, v___x_3142_, v___x_3143_, v___x_3144_, v___f_3141_, v_cleanupAnnotations_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3145_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3145_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg___boxed(lean_object* v_e_3162_, lean_object* v_k_3163_, lean_object* v_cleanupAnnotations_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3170_; lean_object* v_res_3171_; 
v_cleanupAnnotations_boxed_3170_ = lean_unbox(v_cleanupAnnotations_3164_);
v_res_3171_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3162_, v_k_3163_, v_cleanupAnnotations_boxed_3170_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(lean_object* v_00_u03b1_3172_, lean_object* v_e_3173_, lean_object* v_k_3174_, uint8_t v_cleanupAnnotations_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_e_3173_, v_k_3174_, v_cleanupAnnotations_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___boxed(lean_object* v_00_u03b1_3182_, lean_object* v_e_3183_, lean_object* v_k_3184_, lean_object* v_cleanupAnnotations_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3191_; lean_object* v_res_3192_; 
v_cleanupAnnotations_boxed_3191_ = lean_unbox(v_cleanupAnnotations_3185_);
v_res_3192_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3(v_00_u03b1_3182_, v_e_3183_, v_k_3184_, v_cleanupAnnotations_boxed_3191_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(lean_object* v___y_3193_, uint8_t v_isExporting_3194_, lean_object* v___x_3195_, lean_object* v___y_3196_, lean_object* v___x_3197_, lean_object* v_a_x3f_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v_env_3201_; lean_object* v_nextMacroScope_3202_; lean_object* v_ngen_3203_; lean_object* v_auxDeclNGen_3204_; lean_object* v_traceState_3205_; lean_object* v_messages_3206_; lean_object* v_infoState_3207_; lean_object* v_snapshotTasks_3208_; lean_object* v_newDecls_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3234_; 
v___x_3200_ = lean_st_ref_take(v___y_3193_);
v_env_3201_ = lean_ctor_get(v___x_3200_, 0);
v_nextMacroScope_3202_ = lean_ctor_get(v___x_3200_, 1);
v_ngen_3203_ = lean_ctor_get(v___x_3200_, 2);
v_auxDeclNGen_3204_ = lean_ctor_get(v___x_3200_, 3);
v_traceState_3205_ = lean_ctor_get(v___x_3200_, 4);
v_messages_3206_ = lean_ctor_get(v___x_3200_, 6);
v_infoState_3207_ = lean_ctor_get(v___x_3200_, 7);
v_snapshotTasks_3208_ = lean_ctor_get(v___x_3200_, 8);
v_newDecls_3209_ = lean_ctor_get(v___x_3200_, 9);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v___x_3200_, 5);
lean_dec(v_unused_3235_);
v___x_3211_ = v___x_3200_;
v_isShared_3212_ = v_isSharedCheck_3234_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_newDecls_3209_);
lean_inc(v_snapshotTasks_3208_);
lean_inc(v_infoState_3207_);
lean_inc(v_messages_3206_);
lean_inc(v_traceState_3205_);
lean_inc(v_auxDeclNGen_3204_);
lean_inc(v_ngen_3203_);
lean_inc(v_nextMacroScope_3202_);
lean_inc(v_env_3201_);
lean_dec(v___x_3200_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3234_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3215_; 
v___x_3213_ = l_Lean_Environment_setExporting(v_env_3201_, v_isExporting_3194_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 5, v___x_3195_);
lean_ctor_set(v___x_3211_, 0, v___x_3213_);
v___x_3215_ = v___x_3211_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3213_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v_nextMacroScope_3202_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_ngen_3203_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_auxDeclNGen_3204_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_traceState_3205_);
lean_ctor_set(v_reuseFailAlloc_3233_, 5, v___x_3195_);
lean_ctor_set(v_reuseFailAlloc_3233_, 6, v_messages_3206_);
lean_ctor_set(v_reuseFailAlloc_3233_, 7, v_infoState_3207_);
lean_ctor_set(v_reuseFailAlloc_3233_, 8, v_snapshotTasks_3208_);
lean_ctor_set(v_reuseFailAlloc_3233_, 9, v_newDecls_3209_);
v___x_3215_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v_mctx_3218_; lean_object* v_zetaDeltaFVarIds_3219_; lean_object* v_postponed_3220_; lean_object* v_diag_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3231_; 
v___x_3216_ = lean_st_ref_set(v___y_3193_, v___x_3215_);
v___x_3217_ = lean_st_ref_take(v___y_3196_);
v_mctx_3218_ = lean_ctor_get(v___x_3217_, 0);
v_zetaDeltaFVarIds_3219_ = lean_ctor_get(v___x_3217_, 2);
v_postponed_3220_ = lean_ctor_get(v___x_3217_, 3);
v_diag_3221_ = lean_ctor_get(v___x_3217_, 4);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3231_ == 0)
{
lean_object* v_unused_3232_; 
v_unused_3232_ = lean_ctor_get(v___x_3217_, 1);
lean_dec(v_unused_3232_);
v___x_3223_ = v___x_3217_;
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_diag_3221_);
lean_inc(v_postponed_3220_);
lean_inc(v_zetaDeltaFVarIds_3219_);
lean_inc(v_mctx_3218_);
lean_dec(v___x_3217_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 1, v___x_3197_);
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_mctx_3218_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v___x_3197_);
lean_ctor_set(v_reuseFailAlloc_3230_, 2, v_zetaDeltaFVarIds_3219_);
lean_ctor_set(v_reuseFailAlloc_3230_, 3, v_postponed_3220_);
lean_ctor_set(v_reuseFailAlloc_3230_, 4, v_diag_3221_);
v___x_3226_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_st_ref_set(v___y_3196_, v___x_3226_);
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
return v___x_3229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_3236_, lean_object* v_isExporting_3237_, lean_object* v___x_3238_, lean_object* v___y_3239_, lean_object* v___x_3240_, lean_object* v_a_x3f_3241_, lean_object* v___y_3242_){
_start:
{
uint8_t v_isExporting_boxed_3243_; lean_object* v_res_3244_; 
v_isExporting_boxed_3243_ = lean_unbox(v_isExporting_3237_);
v_res_3244_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3236_, v_isExporting_boxed_3243_, v___x_3238_, v___y_3239_, v___x_3240_, v_a_x3f_3241_);
lean_dec(v_a_x3f_3241_);
lean_dec(v___y_3239_);
lean_dec(v___y_3236_);
return v_res_3244_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__1, &l_Lean_Elab_Structural_registerEqnsInfo___closed__1_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__1);
v___x_3246_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
lean_ctor_set(v___x_3246_, 2, v___x_3245_);
lean_ctor_set(v___x_3246_, 3, v___x_3245_);
lean_ctor_set(v___x_3246_, 4, v___x_3245_);
lean_ctor_set(v___x_3246_, 5, v___x_3245_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(lean_object* v_x_3247_, uint8_t v_isExporting_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_){
_start:
{
lean_object* v___x_3254_; lean_object* v_env_3255_; uint8_t v_isExporting_3256_; lean_object* v___x_3257_; lean_object* v_env_3258_; lean_object* v_nextMacroScope_3259_; lean_object* v_ngen_3260_; lean_object* v_auxDeclNGen_3261_; lean_object* v_traceState_3262_; lean_object* v_messages_3263_; lean_object* v_infoState_3264_; lean_object* v_snapshotTasks_3265_; lean_object* v_newDecls_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3320_; 
v___x_3254_ = lean_st_ref_get(v___y_3252_);
v_env_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc_ref(v_env_3255_);
lean_dec(v___x_3254_);
v_isExporting_3256_ = lean_ctor_get_uint8(v_env_3255_, sizeof(void*)*8);
lean_dec_ref(v_env_3255_);
v___x_3257_ = lean_st_ref_take(v___y_3252_);
v_env_3258_ = lean_ctor_get(v___x_3257_, 0);
v_nextMacroScope_3259_ = lean_ctor_get(v___x_3257_, 1);
v_ngen_3260_ = lean_ctor_get(v___x_3257_, 2);
v_auxDeclNGen_3261_ = lean_ctor_get(v___x_3257_, 3);
v_traceState_3262_ = lean_ctor_get(v___x_3257_, 4);
v_messages_3263_ = lean_ctor_get(v___x_3257_, 6);
v_infoState_3264_ = lean_ctor_get(v___x_3257_, 7);
v_snapshotTasks_3265_ = lean_ctor_get(v___x_3257_, 8);
v_newDecls_3266_ = lean_ctor_get(v___x_3257_, 9);
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
lean_inc(v_newDecls_3266_);
lean_inc(v_snapshotTasks_3265_);
lean_inc(v_infoState_3264_);
lean_inc(v_messages_3263_);
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
v___x_3270_ = l_Lean_Environment_setExporting(v_env_3258_, v_isExporting_3248_);
v___x_3271_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
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
lean_ctor_set(v_reuseFailAlloc_3319_, 6, v_messages_3263_);
lean_ctor_set(v_reuseFailAlloc_3319_, 7, v_infoState_3264_);
lean_ctor_set(v_reuseFailAlloc_3319_, 8, v_snapshotTasks_3265_);
lean_ctor_set(v_reuseFailAlloc_3319_, 9, v_newDecls_3266_);
v___x_3273_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v_mctx_3276_; lean_object* v_zetaDeltaFVarIds_3277_; lean_object* v_postponed_3278_; lean_object* v_diag_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3317_; 
v___x_3274_ = lean_st_ref_set(v___y_3252_, v___x_3273_);
v___x_3275_ = lean_st_ref_take(v___y_3250_);
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
v___x_3286_ = lean_st_ref_set(v___y_3250_, v___x_3285_);
lean_inc(v___y_3252_);
lean_inc_ref(v___y_3251_);
lean_inc(v___y_3250_);
lean_inc_ref(v___y_3249_);
v_r_3287_ = lean_apply_5(v_x_3247_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, lean_box(0));
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
v___x_3294_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3252_, v_isExporting_3256_, v___x_3271_, v___y_3250_, v___x_3283_, v___x_3293_);
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
lean_dec_ref(v_r_3287_);
v___x_3306_ = lean_box(0);
v___x_3307_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___lam__0(v___y_3252_, v_isExporting_3256_, v___x_3271_, v___y_3250_, v___x_3283_, v___x_3306_);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg___boxed(lean_object* v_x_3322_, lean_object* v_isExporting_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v_isExporting_boxed_3329_; lean_object* v_res_3330_; 
v_isExporting_boxed_3329_ = lean_unbox(v_isExporting_3323_);
v_res_3330_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3322_, v_isExporting_boxed_3329_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(lean_object* v_x_3331_, uint8_t v_when_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
if (v_when_3332_ == 0)
{
lean_object* v___x_3338_; 
lean_inc(v___y_3336_);
lean_inc_ref(v___y_3335_);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
v___x_3338_ = lean_apply_5(v_x_3331_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, lean_box(0));
return v___x_3338_;
}
else
{
uint8_t v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = 0;
v___x_3340_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3331_, v___x_3339_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
return v___x_3340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg___boxed(lean_object* v_x_3341_, lean_object* v_when_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
uint8_t v_when_boxed_3348_; lean_object* v_res_3349_; 
v_when_boxed_3348_ = lean_unbox(v_when_3342_);
v_res_3349_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3341_, v_when_boxed_3348_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(lean_object* v_a_3350_, lean_object* v_a_3351_){
_start:
{
if (lean_obj_tag(v_a_3350_) == 0)
{
lean_object* v___x_3352_; 
v___x_3352_ = l_List_reverse___redArg(v_a_3351_);
return v___x_3352_;
}
else
{
lean_object* v_head_3353_; lean_object* v_tail_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3363_; 
v_head_3353_ = lean_ctor_get(v_a_3350_, 0);
v_tail_3354_ = lean_ctor_get(v_a_3350_, 1);
v_isSharedCheck_3363_ = !lean_is_exclusive(v_a_3350_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3356_ = v_a_3350_;
v_isShared_3357_ = v_isSharedCheck_3363_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_tail_3354_);
lean_inc(v_head_3353_);
lean_dec(v_a_3350_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3363_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3358_ = l_Lean_mkLevelParam(v_head_3353_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 1, v_a_3351_);
lean_ctor_set(v___x_3356_, 0, v___x_3358_);
v___x_3360_ = v___x_3356_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_a_3351_);
v___x_3360_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
v_a_3350_ = v_tail_3354_;
v_a_3351_ = v___x_3360_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* v_levelParams_3364_, lean_object* v_declName_3365_, lean_object* v_name_3366_, lean_object* v_xs_3367_, lean_object* v_body_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; lean_object* v_us_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3374_ = lean_box(0);
lean_inc(v_levelParams_3364_);
v_us_3375_ = l_List_mapTR_loop___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__0(v_levelParams_3364_, v___x_3374_);
lean_inc(v_declName_3365_);
v___x_3376_ = l_Lean_mkConst(v_declName_3365_, v_us_3375_);
v___x_3377_ = l_Lean_mkAppN(v___x_3376_, v_xs_3367_);
v___x_3378_ = l_Lean_Meta_mkEq(v___x_3377_, v_body_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; lean_object* v___x_3382_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc_n(v_a_3379_, 2);
lean_dec_ref(v___x_3378_);
v___x_3380_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___boxed), 7, 2);
lean_closure_set(v___x_3380_, 0, v_declName_3365_);
lean_closure_set(v___x_3380_, 1, v_a_3379_);
v___x_3381_ = 1;
v___x_3382_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v___x_3380_, v___x_3381_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; uint8_t v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref(v___x_3382_);
v___x_3384_ = 0;
v___x_3385_ = 1;
v___x_3386_ = l_Lean_Meta_mkForallFVars(v_xs_3367_, v_a_3379_, v___x_3384_, v___x_3381_, v___x_3381_, v___x_3385_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3388_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
lean_dec_ref(v___x_3386_);
v___x_3388_ = l_Lean_Meta_letToHave(v_a_3387_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref(v___x_3388_);
v___x_3390_ = l_Lean_Meta_mkLambdaFVars(v_xs_3367_, v_a_3383_, v___x_3384_, v___x_3381_, v___x_3384_, v___x_3381_, v___x_3385_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref(v___x_3390_);
lean_inc_n(v_name_3366_, 2);
v___x_3392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3392_, 0, v_name_3366_);
lean_ctor_set(v___x_3392_, 1, v_levelParams_3364_);
lean_ctor_set(v___x_3392_, 2, v_a_3389_);
v___x_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3393_, 0, v_name_3366_);
lean_ctor_set(v___x_3393_, 1, v___x_3374_);
v___x_3394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3392_);
lean_ctor_set(v___x_3394_, 1, v_a_3391_);
lean_ctor_set(v___x_3394_, 2, v___x_3393_);
v___x_3395_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
v___x_3396_ = l_Lean_addDecl(v___x_3395_, v___x_3384_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3397_; 
lean_dec_ref(v___x_3396_);
v___x_3397_ = l_Lean_inferDefEqAttr(v_name_3366_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
return v___x_3397_;
}
else
{
lean_dec(v_name_3366_);
return v___x_3396_;
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec(v_a_3389_);
lean_dec(v_name_3366_);
lean_dec(v_levelParams_3364_);
v_a_3398_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3390_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3390_);
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
lean_dec(v_a_3383_);
lean_dec(v_name_3366_);
lean_dec(v_levelParams_3364_);
v_a_3406_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3388_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3388_);
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
lean_dec(v_a_3383_);
lean_dec(v_name_3366_);
lean_dec(v_levelParams_3364_);
v_a_3414_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3386_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3386_);
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
lean_dec(v_a_3379_);
lean_dec(v_name_3366_);
lean_dec(v_levelParams_3364_);
v_a_3422_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3424_ = v___x_3382_;
v_isShared_3425_ = v_isSharedCheck_3429_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3382_);
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
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_name_3366_);
lean_dec(v_declName_3365_);
lean_dec(v_levelParams_3364_);
v_a_3430_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3378_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3378_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* v_levelParams_3438_, lean_object* v_declName_3439_, lean_object* v_name_3440_, lean_object* v_xs_3441_, lean_object* v_body_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(v_levelParams_3438_, v_declName_3439_, v_name_3440_, v_xs_3441_, v_body_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec_ref(v___y_3443_);
lean_dec_ref(v_xs_3441_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(lean_object* v_o_3449_, lean_object* v_k_3450_, uint8_t v_v_3451_){
_start:
{
lean_object* v_map_3452_; uint8_t v_hasTrace_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3467_; 
v_map_3452_ = lean_ctor_get(v_o_3449_, 0);
v_hasTrace_3453_ = lean_ctor_get_uint8(v_o_3449_, sizeof(void*)*1);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_o_3449_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3455_ = v_o_3449_;
v_isShared_3456_ = v_isSharedCheck_3467_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_map_3452_);
lean_dec(v_o_3449_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3467_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3457_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_3457_, 0, v_v_3451_);
lean_inc(v_k_3450_);
v___x_3458_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3450_, v___x_3457_, v_map_3452_);
if (v_hasTrace_3453_ == 0)
{
lean_object* v___x_3459_; uint8_t v___x_3460_; lean_object* v___x_3462_; 
v___x_3459_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__19));
v___x_3460_ = l_Lean_Name_isPrefixOf(v___x_3459_, v_k_3450_);
lean_dec(v_k_3450_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3458_);
v___x_3462_ = v___x_3455_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3458_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_ctor_set_uint8(v___x_3462_, sizeof(void*)*1, v___x_3460_);
return v___x_3462_;
}
}
else
{
lean_object* v___x_3465_; 
lean_dec(v_k_3450_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3458_);
v___x_3465_ = v___x_3455_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3458_);
lean_ctor_set_uint8(v_reuseFailAlloc_3466_, sizeof(void*)*1, v_hasTrace_3453_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3___boxed(lean_object* v_o_3468_, lean_object* v_k_3469_, lean_object* v_v_3470_){
_start:
{
uint8_t v_v_boxed_3471_; lean_object* v_res_3472_; 
v_v_boxed_3471_ = lean_unbox(v_v_3470_);
v_res_3472_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_o_3468_, v_k_3469_, v_v_boxed_3471_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(lean_object* v_opts_3473_, lean_object* v_opt_3474_, uint8_t v_val_3475_){
_start:
{
lean_object* v_name_3476_; lean_object* v___x_3477_; 
v_name_3476_ = lean_ctor_get(v_opt_3474_, 0);
lean_inc(v_name_3476_);
lean_dec_ref(v_opt_3474_);
v___x_3477_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2_spec__3(v_opts_3473_, v_name_3476_, v_val_3475_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2___boxed(lean_object* v_opts_3478_, lean_object* v_opt_3479_, lean_object* v_val_3480_){
_start:
{
uint8_t v_val_boxed_3481_; lean_object* v_res_3482_; 
v_val_boxed_3481_ = lean_unbox(v_val_3480_);
v_res_3482_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_opts_3478_, v_opt_3479_, v_val_boxed_3481_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* v_declName_3483_, lean_object* v_info_3484_, lean_object* v_name_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v___x_3491_; lean_object* v_levelParams_3492_; lean_object* v_value_3493_; lean_object* v_fileName_3494_; lean_object* v_fileMap_3495_; lean_object* v_options_3496_; lean_object* v_currRecDepth_3497_; lean_object* v_ref_3498_; lean_object* v_currNamespace_3499_; lean_object* v_openDecls_3500_; lean_object* v_initHeartbeats_3501_; lean_object* v_maxHeartbeats_3502_; lean_object* v_quotContext_3503_; lean_object* v_currMacroScope_3504_; lean_object* v_cancelTk_x3f_3505_; uint8_t v_suppressElabErrors_3506_; lean_object* v_inheritedTraceOptions_3507_; lean_object* v_env_3508_; lean_object* v___f_3509_; uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; lean_object* v_fileName_3516_; lean_object* v_fileMap_3517_; lean_object* v_currRecDepth_3518_; lean_object* v_ref_3519_; lean_object* v_currNamespace_3520_; lean_object* v_openDecls_3521_; lean_object* v_initHeartbeats_3522_; lean_object* v_maxHeartbeats_3523_; lean_object* v_quotContext_3524_; lean_object* v_currMacroScope_3525_; lean_object* v_cancelTk_x3f_3526_; uint8_t v_suppressElabErrors_3527_; lean_object* v_inheritedTraceOptions_3528_; lean_object* v___y_3529_; uint8_t v___y_3535_; uint8_t v___x_3557_; 
v___x_3491_ = lean_st_ref_get(v_a_3489_);
v_levelParams_3492_ = lean_ctor_get(v_info_3484_, 1);
lean_inc(v_levelParams_3492_);
v_value_3493_ = lean_ctor_get(v_info_3484_, 3);
lean_inc_ref(v_value_3493_);
lean_dec_ref(v_info_3484_);
v_fileName_3494_ = lean_ctor_get(v_a_3488_, 0);
v_fileMap_3495_ = lean_ctor_get(v_a_3488_, 1);
v_options_3496_ = lean_ctor_get(v_a_3488_, 2);
v_currRecDepth_3497_ = lean_ctor_get(v_a_3488_, 3);
v_ref_3498_ = lean_ctor_get(v_a_3488_, 5);
v_currNamespace_3499_ = lean_ctor_get(v_a_3488_, 6);
v_openDecls_3500_ = lean_ctor_get(v_a_3488_, 7);
v_initHeartbeats_3501_ = lean_ctor_get(v_a_3488_, 8);
v_maxHeartbeats_3502_ = lean_ctor_get(v_a_3488_, 9);
v_quotContext_3503_ = lean_ctor_get(v_a_3488_, 10);
v_currMacroScope_3504_ = lean_ctor_get(v_a_3488_, 11);
v_cancelTk_x3f_3505_ = lean_ctor_get(v_a_3488_, 12);
v_suppressElabErrors_3506_ = lean_ctor_get_uint8(v_a_3488_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3507_ = lean_ctor_get(v_a_3488_, 13);
v_env_3508_ = lean_ctor_get(v___x_3491_, 0);
lean_inc_ref(v_env_3508_);
lean_dec(v___x_3491_);
v___f_3509_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3509_, 0, v_levelParams_3492_);
lean_closure_set(v___f_3509_, 1, v_declName_3483_);
lean_closure_set(v___f_3509_, 2, v_name_3485_);
v___x_3510_ = 0;
v___x_3511_ = l_Lean_Meta_tactic_hygienic;
lean_inc_ref(v_options_3496_);
v___x_3512_ = l_Lean_Option_set___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__2(v_options_3496_, v___x_3511_, v___x_3510_);
v___x_3513_ = l_Lean_diagnostics;
v___x_3514_ = l_Lean_Option_get___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__4(v___x_3512_, v___x_3513_);
v___x_3557_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_3508_);
lean_dec_ref(v_env_3508_);
if (v___x_3557_ == 0)
{
if (v___x_3514_ == 0)
{
v_fileName_3516_ = v_fileName_3494_;
v_fileMap_3517_ = v_fileMap_3495_;
v_currRecDepth_3518_ = v_currRecDepth_3497_;
v_ref_3519_ = v_ref_3498_;
v_currNamespace_3520_ = v_currNamespace_3499_;
v_openDecls_3521_ = v_openDecls_3500_;
v_initHeartbeats_3522_ = v_initHeartbeats_3501_;
v_maxHeartbeats_3523_ = v_maxHeartbeats_3502_;
v_quotContext_3524_ = v_quotContext_3503_;
v_currMacroScope_3525_ = v_currMacroScope_3504_;
v_cancelTk_x3f_3526_ = v_cancelTk_x3f_3505_;
v_suppressElabErrors_3527_ = v_suppressElabErrors_3506_;
v_inheritedTraceOptions_3528_ = v_inheritedTraceOptions_3507_;
v___y_3529_ = v_a_3489_;
goto v___jp_3515_;
}
else
{
v___y_3535_ = v___x_3557_;
goto v___jp_3534_;
}
}
else
{
v___y_3535_ = v___x_3514_;
goto v___jp_3534_;
}
v___jp_3515_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3530_ = l_Lean_maxRecDepth;
v___x_3531_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__5_spec__8(v___x_3512_, v___x_3530_);
lean_inc_ref(v_inheritedTraceOptions_3528_);
lean_inc(v_cancelTk_x3f_3526_);
lean_inc(v_currMacroScope_3525_);
lean_inc(v_quotContext_3524_);
lean_inc(v_maxHeartbeats_3523_);
lean_inc(v_initHeartbeats_3522_);
lean_inc(v_openDecls_3521_);
lean_inc(v_currNamespace_3520_);
lean_inc(v_ref_3519_);
lean_inc(v_currRecDepth_3518_);
lean_inc_ref(v_fileMap_3517_);
lean_inc_ref(v_fileName_3516_);
v___x_3532_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3532_, 0, v_fileName_3516_);
lean_ctor_set(v___x_3532_, 1, v_fileMap_3517_);
lean_ctor_set(v___x_3532_, 2, v___x_3512_);
lean_ctor_set(v___x_3532_, 3, v_currRecDepth_3518_);
lean_ctor_set(v___x_3532_, 4, v___x_3531_);
lean_ctor_set(v___x_3532_, 5, v_ref_3519_);
lean_ctor_set(v___x_3532_, 6, v_currNamespace_3520_);
lean_ctor_set(v___x_3532_, 7, v_openDecls_3521_);
lean_ctor_set(v___x_3532_, 8, v_initHeartbeats_3522_);
lean_ctor_set(v___x_3532_, 9, v_maxHeartbeats_3523_);
lean_ctor_set(v___x_3532_, 10, v_quotContext_3524_);
lean_ctor_set(v___x_3532_, 11, v_currMacroScope_3525_);
lean_ctor_set(v___x_3532_, 12, v_cancelTk_x3f_3526_);
lean_ctor_set(v___x_3532_, 13, v_inheritedTraceOptions_3528_);
lean_ctor_set_uint8(v___x_3532_, sizeof(void*)*14, v___x_3514_);
lean_ctor_set_uint8(v___x_3532_, sizeof(void*)*14 + 1, v_suppressElabErrors_3527_);
v___x_3533_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__3___redArg(v_value_3493_, v___f_3509_, v___x_3510_, v_a_3486_, v_a_3487_, v___x_3532_, v___y_3529_);
lean_dec_ref(v___x_3532_);
return v___x_3533_;
}
v___jp_3534_:
{
if (v___y_3535_ == 0)
{
lean_object* v___x_3536_; lean_object* v_env_3537_; lean_object* v_nextMacroScope_3538_; lean_object* v_ngen_3539_; lean_object* v_auxDeclNGen_3540_; lean_object* v_traceState_3541_; lean_object* v_messages_3542_; lean_object* v_infoState_3543_; lean_object* v_snapshotTasks_3544_; lean_object* v_newDecls_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3555_; 
v___x_3536_ = lean_st_ref_take(v_a_3489_);
v_env_3537_ = lean_ctor_get(v___x_3536_, 0);
v_nextMacroScope_3538_ = lean_ctor_get(v___x_3536_, 1);
v_ngen_3539_ = lean_ctor_get(v___x_3536_, 2);
v_auxDeclNGen_3540_ = lean_ctor_get(v___x_3536_, 3);
v_traceState_3541_ = lean_ctor_get(v___x_3536_, 4);
v_messages_3542_ = lean_ctor_get(v___x_3536_, 6);
v_infoState_3543_ = lean_ctor_get(v___x_3536_, 7);
v_snapshotTasks_3544_ = lean_ctor_get(v___x_3536_, 8);
v_newDecls_3545_ = lean_ctor_get(v___x_3536_, 9);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3555_ == 0)
{
lean_object* v_unused_3556_; 
v_unused_3556_ = lean_ctor_get(v___x_3536_, 5);
lean_dec(v_unused_3556_);
v___x_3547_ = v___x_3536_;
v_isShared_3548_ = v_isSharedCheck_3555_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_newDecls_3545_);
lean_inc(v_snapshotTasks_3544_);
lean_inc(v_infoState_3543_);
lean_inc(v_messages_3542_);
lean_inc(v_traceState_3541_);
lean_inc(v_auxDeclNGen_3540_);
lean_inc(v_ngen_3539_);
lean_inc(v_nextMacroScope_3538_);
lean_inc(v_env_3537_);
lean_dec(v___x_3536_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3555_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3549_ = l_Lean_Kernel_enableDiag(v_env_3537_, v___x_3514_);
v___x_3550_ = lean_obj_once(&l_Lean_Elab_Structural_registerEqnsInfo___closed__2, &l_Lean_Elab_Structural_registerEqnsInfo___closed__2_once, _init_l_Lean_Elab_Structural_registerEqnsInfo___closed__2);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 5, v___x_3550_);
lean_ctor_set(v___x_3547_, 0, v___x_3549_);
v___x_3552_ = v___x_3547_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v_nextMacroScope_3538_);
lean_ctor_set(v_reuseFailAlloc_3554_, 2, v_ngen_3539_);
lean_ctor_set(v_reuseFailAlloc_3554_, 3, v_auxDeclNGen_3540_);
lean_ctor_set(v_reuseFailAlloc_3554_, 4, v_traceState_3541_);
lean_ctor_set(v_reuseFailAlloc_3554_, 5, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3554_, 6, v_messages_3542_);
lean_ctor_set(v_reuseFailAlloc_3554_, 7, v_infoState_3543_);
lean_ctor_set(v_reuseFailAlloc_3554_, 8, v_snapshotTasks_3544_);
lean_ctor_set(v_reuseFailAlloc_3554_, 9, v_newDecls_3545_);
v___x_3552_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_st_ref_set(v_a_3489_, v___x_3552_);
v_fileName_3516_ = v_fileName_3494_;
v_fileMap_3517_ = v_fileMap_3495_;
v_currRecDepth_3518_ = v_currRecDepth_3497_;
v_ref_3519_ = v_ref_3498_;
v_currNamespace_3520_ = v_currNamespace_3499_;
v_openDecls_3521_ = v_openDecls_3500_;
v_initHeartbeats_3522_ = v_initHeartbeats_3501_;
v_maxHeartbeats_3523_ = v_maxHeartbeats_3502_;
v_quotContext_3524_ = v_quotContext_3503_;
v_currMacroScope_3525_ = v_currMacroScope_3504_;
v_cancelTk_x3f_3526_ = v_cancelTk_x3f_3505_;
v_suppressElabErrors_3527_ = v_suppressElabErrors_3506_;
v_inheritedTraceOptions_3528_ = v_inheritedTraceOptions_3507_;
v___y_3529_ = v_a_3489_;
goto v___jp_3515_;
}
}
}
else
{
v_fileName_3516_ = v_fileName_3494_;
v_fileMap_3517_ = v_fileMap_3495_;
v_currRecDepth_3518_ = v_currRecDepth_3497_;
v_ref_3519_ = v_ref_3498_;
v_currNamespace_3520_ = v_currNamespace_3499_;
v_openDecls_3521_ = v_openDecls_3500_;
v_initHeartbeats_3522_ = v_initHeartbeats_3501_;
v_maxHeartbeats_3523_ = v_maxHeartbeats_3502_;
v_quotContext_3524_ = v_quotContext_3503_;
v_currMacroScope_3525_ = v_currMacroScope_3504_;
v_cancelTk_x3f_3526_ = v_cancelTk_x3f_3505_;
v_suppressElabErrors_3527_ = v_suppressElabErrors_3506_;
v_inheritedTraceOptions_3528_ = v_inheritedTraceOptions_3507_;
v___y_3529_ = v_a_3489_;
goto v___jp_3515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed(lean_object* v_declName_3558_, lean_object* v_info_3559_, lean_object* v_name_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize(v_declName_3558_, v_info_3559_, v_name_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(lean_object* v_00_u03b1_3567_, lean_object* v_x_3568_, uint8_t v_isExporting_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___redArg(v_x_3568_, v_isExporting_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1___boxed(lean_object* v_00_u03b1_3576_, lean_object* v_x_3577_, lean_object* v_isExporting_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
uint8_t v_isExporting_boxed_3584_; lean_object* v_res_3585_; 
v_isExporting_boxed_3584_ = lean_unbox(v_isExporting_3578_);
v_res_3585_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1_spec__1(v_00_u03b1_3576_, v_x_3577_, v_isExporting_boxed_3584_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
lean_dec(v___y_3580_);
lean_dec_ref(v___y_3579_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(lean_object* v_00_u03b1_3586_, lean_object* v_x_3587_, uint8_t v_when_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___redArg(v_x_3587_, v_when_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1___boxed(lean_object* v_00_u03b1_3595_, lean_object* v_x_3596_, lean_object* v_when_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
uint8_t v_when_boxed_3603_; lean_object* v_res_3604_; 
v_when_boxed_3603_ = lean_unbox(v_when_3597_);
v_res_3604_ = l_Lean_withoutExporting___at___00__private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize_spec__1(v_00_u03b1_3595_, v_x_3596_, v_when_boxed_3603_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(lean_object* v_declName_3605_, lean_object* v_info_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_){
_start:
{
lean_object* v___x_3612_; lean_object* v_env_3613_; lean_object* v_declName_3614_; lean_object* v_declNames_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3612_ = lean_st_ref_get(v_a_3610_);
v_env_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc_ref(v_env_3613_);
lean_dec(v___x_3612_);
v_declName_3614_ = lean_ctor_get(v_info_3606_, 0);
v_declNames_3615_ = lean_ctor_get(v_info_3606_, 5);
v___x_3616_ = lean_box(0);
v___x_3617_ = l_Lean_Meta_unfoldThmSuffix;
lean_inc(v_declName_3614_);
v___x_3618_ = l_Lean_Meta_mkEqLikeNameFor(v_env_3613_, v_declName_3614_, v___x_3617_);
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = lean_array_get(v___x_3616_, v_declNames_3615_, v___x_3619_);
lean_inc_n(v___x_3618_, 2);
lean_inc(v_declName_3605_);
v___x_3621_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq_doRealize___boxed), 8, 3);
lean_closure_set(v___x_3621_, 0, v_declName_3605_);
lean_closure_set(v___x_3621_, 1, v_info_3606_);
lean_closure_set(v___x_3621_, 2, v___x_3618_);
v___x_3622_ = lean_alloc_closure((void*)(l_Lean_Meta_withEqnOptions___boxed), 8, 3);
lean_closure_set(v___x_3622_, 0, lean_box(0));
lean_closure_set(v___x_3622_, 1, v_declName_3605_);
lean_closure_set(v___x_3622_, 2, v___x_3621_);
v___x_3623_ = l_Lean_Meta_realizeConst(v___x_3620_, v___x_3618_, v___x_3622_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3630_ == 0)
{
lean_object* v_unused_3631_; 
v_unused_3631_ = lean_ctor_get(v___x_3623_, 0);
lean_dec(v_unused_3631_);
v___x_3625_ = v___x_3623_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_dec(v___x_3623_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v___x_3618_);
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3618_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v___x_3618_);
v_a_3632_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3623_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3623_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq___boxed(lean_object* v_declName_3640_, lean_object* v_info_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3640_, v_info_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* v_declName_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v_env_3655_; lean_object* v___x_3656_; lean_object* v_toEnvExtension_3657_; lean_object* v_asyncMode_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; lean_object* v___x_3661_; 
v___x_3654_ = lean_st_ref_get(v_a_3652_);
v_env_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc_ref(v_env_3655_);
lean_dec(v___x_3654_);
v___x_3656_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3657_ = lean_ctor_get(v___x_3656_, 0);
v_asyncMode_3658_ = lean_ctor_get(v_toEnvExtension_3657_, 2);
v___x_3659_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3660_ = 0;
lean_inc(v_declName_3648_);
v___x_3661_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3659_, v___x_3656_, v_env_3655_, v_declName_3648_, v_asyncMode_3658_, v___x_3660_);
if (lean_obj_tag(v___x_3661_) == 1)
{
lean_object* v_val_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3686_; 
v_val_3662_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3664_ = v___x_3661_;
v_isShared_3665_ = v_isSharedCheck_3686_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_val_3662_);
lean_dec(v___x_3661_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3686_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; 
v___x_3666_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkUnfoldEq(v_declName_3648_, v_val_3662_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3677_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3677_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3677_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set(v___x_3664_, 0, v_a_3667_);
v___x_3672_ = v___x_3664_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3674_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3672_);
v___x_3674_ = v___x_3669_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3672_);
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
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_del_object(v___x_3664_);
v_a_3678_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3666_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3666_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
lean_dec(v___x_3661_);
lean_dec(v_declName_3648_);
v___x_3687_ = lean_box(0);
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
return v___x_3688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f___boxed(lean_object* v_declName_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getUnfoldFor_x3f(v_declName_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* v_declName_3696_, lean_object* v_a_3697_){
_start:
{
lean_object* v___x_3699_; lean_object* v_env_3700_; lean_object* v___x_3701_; lean_object* v_toEnvExtension_3702_; lean_object* v_asyncMode_3703_; lean_object* v___x_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; 
v___x_3699_ = lean_st_ref_get(v_a_3697_);
v_env_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc_ref(v_env_3700_);
lean_dec(v___x_3699_);
v___x_3701_ = l_Lean_Elab_Structural_eqnInfoExt;
v_toEnvExtension_3702_ = lean_ctor_get(v___x_3701_, 0);
v_asyncMode_3703_ = lean_ctor_get(v_toEnvExtension_3702_, 2);
v___x_3704_ = l_Lean_Elab_Structural_instInhabitedEqnInfo_default;
v___x_3705_ = 0;
v___x_3706_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3704_, v___x_3701_, v_env_3700_, v_declName_3696_, v_asyncMode_3703_, v___x_3705_);
if (lean_obj_tag(v___x_3706_) == 1)
{
lean_object* v_val_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3716_; 
v_val_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3716_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_val_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3716_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v_recArgPos_3711_; lean_object* v___x_3713_; 
v_recArgPos_3711_ = lean_ctor_get(v_val_3707_, 4);
lean_inc(v_recArgPos_3711_);
lean_dec(v_val_3707_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v_recArgPos_3711_);
v___x_3713_ = v___x_3709_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_recArgPos_3711_);
v___x_3713_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
return v___x_3714_;
}
}
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
lean_dec(v___x_3706_);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
return v___x_3718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* v_declName_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3719_, v_a_3720_);
lean_dec(v_a_3720_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* v_declName_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v___x_3727_; 
lean_dec_ref(v_a_3724_);
v___x_3727_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(v_declName_3723_, v_a_3725_);
lean_dec(v_a_3725_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___boxed(lean_object* v_declName_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = lean_get_structural_rec_arg_pos(v_declName_3728_, v_a_3729_, v_a_3730_);
return v_res_3732_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_unsigned_to_nat(2295916746u);
v___x_3791_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3792_ = l_Lean_Name_num___override(v___x_3791_, v___x_3790_);
return v___x_3792_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3795_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3796_ = l_Lean_Name_str___override(v___x_3795_, v___x_3794_);
return v___x_3796_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3798_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3799_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3800_ = l_Lean_Name_str___override(v___x_3799_, v___x_3798_);
return v___x_3800_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_unsigned_to_nat(2u);
v___x_3802_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3803_ = l_Lean_Name_num___override(v___x_3802_, v___x_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_));
v___x_3806_ = l_Lean_Meta_registerGetUnfoldEqnFn(v___x_3805_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v___x_3807_; uint8_t v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
lean_dec_ref(v___x_3806_);
v___x_3807_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go___closed__17));
v___x_3808_ = 0;
v___x_3809_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_, &l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_);
v___x_3810_ = l_Lean_registerTraceClass(v___x_3807_, v___x_3808_, v___x_3809_);
return v___x_3810_;
}
else
{
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2____boxed(lean_object* v_a_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_initFn_00___x40_Lean_Elab_PreDefinition_Structural_Eqns_2295916746____hygCtx___hyg_2_();
return v_res_3812_;
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
